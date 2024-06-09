using System;
using System.CodeDom.Compiler;
using System.Collections.Generic;
using System.Linq;
using Newtonsoft.Json;
using NiL.JS.Expressions;
using PSASM;

namespace ONICPU
{
    public class FCPUExecutorAssemblyCode : FCPUExecutor
    {
        public PSASMContext psasmContext = new();

        public FCPUExecutorAssemblyCode()
        {
            cpuState = FCPUState.NotStart;
            psasmContext.onSync = (ref int input, int output) =>
            {
                this.InputOutput.UpdateInputs();
                input = 0;
                for (int i = 0; i < this.InputOutput.InputValues.Length; i++)
                {
                    input |= (this.InputOutput.InputValues[i] << (i * 4));
                }
                for (int i = 0; i < this.InputOutput.OutputValues.Length; i++)
                {
                    this.InputOutput.Write(i + this.InputOutput.OutputValues.Length, output >> (i * 4));
                }
            };
        }

        private void ResetAll()
        {
            psasmContext.Reset();
            InputOutput.Reset();
        }
        private void HaltAndReportError(string message)
        {
            cpuState = FCPUState.HaltByError;
            onError.Invoke(message);
        }

        public override string CompileProgram(string program)
        {
            try
            {
                if (program.IsNullOrWhiteSpace()) return "";
                ExecuteReset();
                psasmContext.Programming(program);
                return "";
            }
            catch (Exception e)
            {
                return e.Message;
            }
        }

        public override void Init()
        {
        }
        public override bool Restore(in byte[] bytes)
        {
            if (bytes is not null)
            {
                try
                {
                    AsmSerializer.Deserialize(bytes, psasmContext);
                    cpuState = (FCPUState)BitConverter.ToInt32(bytes, bytes.Length - 4);
                    psasmContext.onSync?.Invoke(ref psasmContext.input, psasmContext.output);
                    return true;
                }
                catch (Exception e)
                {
                    HaltAndReportError(e.Message);
                    return false;
                }
            }
            return false;
        }
        public override byte[] Save()
        {
            AsmSerializer.Serialize(psasmContext, out byte[] contextBytes);
            return contextBytes.Concat(BitConverter.GetBytes((int)cpuState));
        }
        public override void Start()
        {
            cpuState = FCPUState.Looping;
        }
        public override void Stop()
        {
            cpuState = FCPUState.HaltByUser;
        }
        public override void ExecuteReset()
        {
            ResetAll();
            cpuState = FCPUState.NotStart;
        }
        public override void ExecuteTick()
        {
            if (cpuState != FCPUState.Looping) return;
            if (!psasmContext.Step())
            {
                throw new Exception("finished");
            }
        }
        public override void ExecuteTicks()
        {
            if (cpuState != FCPUState.Looping) return;
            if (!psasmContext.Steps(10000))
            {
                throw new Exception("finished");
            }
        }
    }
}
