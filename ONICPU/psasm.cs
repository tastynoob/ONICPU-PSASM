using System.Text.RegularExpressions;
using System.Collections.Generic;
using System;
using System.Reflection;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Runtime.Serialization;


namespace PSASM
{
    using RegVal = int;
    /*
    ops:
    imm: 1 2 3
    regid: x0-x7 or ra,sp,s0-s5
    mem: [imm] or [regid] or [[[..]]]

    instructions:
    c[op] dst src1 src2     : dst = src1 op src2
    mv dst src1             : dst = src1
    push src1 src2 ... srcn : push src1, src2, ..., srcn to stack, sp -= n, srcn is on stack head
    pop dst1 dst2 ... dstn  : from stack pop to dstn, ..., dst2, dst1, sp +=n
    b[op] src1 src2 lable   : if src1 op src2 then jump lable
    j lable                 : jump lable
    apc dst offset          : dst = pc + offset
    in dst io (shift)         : dst = dst | (io << shift), shift is optional default is 0, io: 0, 1...
    out io src1 (shift)       : out = (src1 >> shift), , shift is optional default is 0
    sync                    : sync io
    */

    public class PSASMContext : ISaveable
    {
        const int MaxInsts = 128;
        public delegate void IOSync(ref RegVal input, RegVal output);
        readonly AsmParser asmParser = new();
        int numInsts;
        public readonly IAsmInst[] rom;
        public RegVal pc;
        public RegVal[] rf, ram;

        public RegVal input;
        public RegVal output;

        public bool finished = false, sync = false;
        public IOSync? onSync;

        public PSASMContext()
        {
            rom = new IAsmInst[MaxInsts + 20];
            rf = new RegVal[16];
            ram = new RegVal[256];

            Reset();
        }

        public void Reset()
        {
            numInsts = 0;
            pc = 0;
            for (int i = 0; i < (int)AsmParser.RegId.NumRegs; i++) rf[i] = 0;
            rf[(RegVal)AsmParser.RegId.sp] = ram.Length - 1;
            input = 0;
            output = 0;
            finished = false;
            sync = false;
        }

        public void Programming(string program)
        {
            string[] lines = program.Split('\n');
            asmParser.RemoveComments(ref lines);
            asmParser.ScanLable(lines);
            foreach (string line in lines)
            {
                if (line.Length == 0 || line.EndsWith(":")) continue;
                IAsmInst inst = asmParser.ParseInst(line.ToLower());
                PushInst(inst);
            }
            PlaceHolder();
        }

        public bool Steps(int steps)
        {
            for (int i = 0; i < steps && !(finished || sync); i++)
            {
                rom[pc].Execute(this); ++pc;
            }
            if (sync) { sync = false; onSync?.Invoke(ref input, output); }
            return !finished;
        }

        public bool Step() // continue if true
        {
            rom[pc].Execute(this); ++pc;
            if (sync) { sync = false; onSync?.Invoke(ref input, output); }
            return !finished;
        }

        void PushInst(IAsmInst inst)
        {
            if (numInsts >= MaxInsts) throw new Exception("Too many instructions");
            rom[numInsts] = inst;
            numInsts++;
        }

        void PlaceHolder()
        {
            rom[numInsts] = new AsmInstEnd();
            numInsts++;
            for (int i = 0; i < 20; i++)
            {
                rom[numInsts] = new AsmInstNop();
                numInsts++;
            }
        }


        public void Store(in List<uint> lst)
        {
            // serialize rom
            lst.Add((uint)numInsts);
            for (int i = 0; i < numInsts; i++)
            {
                AsmSerializer.SerializeOne(lst, rom[i] as ISaveable ?? throw new Exception("Unknown type: " + rom[i].GetType()));
            }
            // serialize rf
            lst.Add((uint)rf.Length);
            for (int i = 0; i < rf.Length; i++)
            {
                lst.Add((uint)rf[i]);
            }
            // serialize ram
            lst.Add((uint)ram.Length);
            for (int i = 0; i < ram.Length; i++)
            {
                lst.Add((uint)ram[i]);
            }
            // serialize other
            lst.Add((uint)pc);
            lst.Add((uint)input);
            lst.Add((uint)output);
            lst.Add(finished ? 1u : 0u);
            lst.Add(sync ? 1u : 0u);
        }

        public void Load(in IEnumerator<uint> it)
        {
            // load rom
            numInsts = (int)it.Current; it.MoveNext();
            for (int i = 0; i < numInsts; i++)
            {
                rom[i] = AsmSerializer.DeserializeOne(it) as IAsmInst ?? throw new Exception("Invalid instruction, may be a broken serialized data");
            }
            // load rf
            int rfLen = (int)it.Current; it.MoveNext();
            rf = new RegVal[rfLen];
            for (int i = 0; i < rfLen; i++)
            {
                rf[i] = (RegVal)it.Current; it.MoveNext();
            }
            // load ram
            int ramLen = (int)it.Current; it.MoveNext();
            ram = new RegVal[ramLen];
            for (int i = 0; i < ramLen; i++)
            {
                ram[i] = (RegVal)it.Current; it.MoveNext();
            }
            // load other
            pc = (RegVal)it.Current; it.MoveNext();
            input = (RegVal)it.Current; it.MoveNext();
            output = (RegVal)it.Current; it.MoveNext();
            finished = it.Current == 1u; it.MoveNext();
            sync = it.Current == 1u; it.MoveNext();
        }
    }

    class AsmParser
    {
        public enum RegId { ra, sp, s0, s1, s2, s3, s4, s5, NumRegs };

        readonly static Dictionary<string, uint> regidmap = new(){
        // x0-x7   :  alias
        {"x0" , 0 }, {"ra", 0},
        {"x1" , 1 }, {"sp", 1},
        {"x2" , 2 }, {"s0", 2},
        {"x3" , 3 }, {"s1", 3},
        {"x4" , 4 }, {"s2", 4},
        {"x5" , 5 }, {"s3", 5},
        {"x6" , 6 }, {"s4", 6},
        {"x7" , 7 }, {"s5", 7},
    };

        readonly static Regex regexImm = new(@"^(0x)?(-?[0-9]+)");
        readonly static Regex regexMem = new(@"^\[(.*)\]");

        #region
        readonly static Dictionary<string, ALUInstFactory> alInst = new(){
        {"+" , (dst, src1, src2) => (dst, src1, src2) switch
        {
            (RegOpParam p1, RegOpParam p2, ImmOpParam p3) => new AsmInstAddOptRRI(p1.regid, p2.regid, p3.imm),
            (RegOpParam p1, ImmOpParam p3, RegOpParam p2) => new AsmInstAddOptRRI(p1.regid, p2.regid, p3.imm),
            _ => new AsmInstAdd(dst, src1, src2)
        }},
        {"-", (dst, src1, src2) => new AsmInstSub(dst, src1, src2)},
        {"&", (dst, src1, src2) => new AsmInstAnd(dst, src1, src2)},
        {"|", (dst, src1, src2) => new AsmInstOr(dst, src1, src2)},
        {"^", (dst, src1, src2) => new AsmInstXor(dst, src1, src2)},
        {"<<", (dst, src1, src2) => new AsmInstSll(dst, src1, src2)},
        {">>>", (dst, src1, src2) => new AsmInstSrl(dst, src1, src2)},
        {">>", (dst, src1, src2) => new AsmInstSra(dst, src1, src2)},
        {"==", (dst, src1, src2) => new AsmInstEq(dst, src1, src2)},
        {"!=", (dst, src1, src2) => new AsmInstNe(dst, src1, src2)},
        {"<", (dst, src1, src2) => new AsmInstLt(dst, src1, src2)},
        {">=", (dst, src1, src2) => new AsmInstGte(dst, src1, src2)},
        {">", (dst, src1, src2) => new AsmInstLt(dst, src2, src1)},
        {"<=", (dst, src1, src2) => new AsmInstGte(dst, src2, src1)},
    };
        readonly static Dictionary<string, BRUInstFactory> brInst = new(){
        {"==" , (src1, src2, target) => new AsmInstBeq(src1, src2, target)},
        {"!=" , (src1, src2, target) => new AsmInstBne(src1, src2, target)},
        {"<" , (src1, src2, target) => new AsmInstBlt(src1, src2, target)},
        {">=" , (src1, src2, target) => new AsmInstBgte(src1, src2, target)},
        {">" , (src1, src2, target) => new AsmInstBlt(src2, src1, target)},
        {"<=" , (src1, src2, target) => new AsmInstBgte(src2, src1, target)},
    };
        readonly static Dictionary<string, BRUInstFactory> brInstOptRR = new(){
        {"==" , (src1, src2, target) => new AsmInstBeqOptRR(((RegOpParam)src1).regid, ((RegOpParam)src2).regid, target)},
        {"!=" , (src1, src2, target) => new AsmInstBneOptRR(((RegOpParam)src1).regid, ((RegOpParam)src2).regid, target)},
        {"<" , (src1, src2, target) => new AsmInstBltOptRR(((RegOpParam)src1).regid, ((RegOpParam)src2).regid, target)},
        {">=" , (src1, src2, target) => new AsmInstBgteOptRR(((RegOpParam)src1).regid, ((RegOpParam)src2).regid, target)},
        {">" , (src1, src2, target) => new AsmInstBltOptRR(((RegOpParam)src2).regid, ((RegOpParam)src1).regid, target)},
        {"<=" , (src1, src2, target) => new AsmInstBgteOptRR(((RegOpParam)src2).regid, ((RegOpParam)src1).regid, target)},
    };
        readonly static Dictionary<string, BRUInstFactory> brInstOptRI = new(){
        {"==" , (src1, src2, target) => new AsmInstBeqOptRI(((RegOpParam)src1).regid, ((ImmOpParam)src2).imm, target)},
        {"!=" , (src1, src2, target) => new AsmInstBneOptRI(((RegOpParam)src1).regid, ((ImmOpParam)src2).imm, target)},
        {"<" , (src1, src2, target) => new AsmInstBltOptRI(((RegOpParam)src1).regid, ((ImmOpParam)src2).imm, target)},
        {">=" , (src1, src2, target) => new AsmInstBgteOptRI(((RegOpParam)src1).regid, ((ImmOpParam)src2).imm, target)},
        {">" , (src1, src2, target) => new AsmInstBltOptRI(((RegOpParam)src2).regid, ((ImmOpParam)src1).imm, target)},
        {"<=" , (src1, src2, target) => new AsmInstBgteOptRI(((RegOpParam)src2).regid, ((ImmOpParam)src1).imm, target)},
    };

        #endregion

        // label point to the next instruction
        readonly Dictionary<string, int> labelTable = [];

        static IOpParam ParseOpParam(in string token)
        {
            MatchCollection match;
            match = regexImm.Matches(token);
            if (match.Count > 0) // imm op
            {
                int imm = 0;
                if (match[0].Groups[1].Value == "0x") imm = int.Parse(match[0].Groups[2].Value, System.Globalization.NumberStyles.HexNumber);
                else imm = int.Parse(match[0].Groups[0].Value);
                return new ImmOpParam(imm);
            }
            match = regexMem.Matches(token);
            if (match.Count > 0) // mem op
            {
                string addr = match[0].Groups[1].Value;
                IOpParam addrOp = ParseOpParam(addr);
                return new MemOpParam(addrOp);
            }
            if (regidmap.TryGetValue(token, out uint value)) // regop
            {
                uint regid = value;
                return new RegOpParam(regid);
            }
            throw new Exception("Invalid operand:" + token);
        }

        public IAsmInst ParseInst(in string inst)
        {
            string[] token = inst.Split(' ');
            string name = token[0];
            if (name.StartsWith("c"))
            {
                if (token.Length != 4) throw new Exception("Invalid cal instruction");
                string op = name.Substring(1);
                if (!alInst.TryGetValue(op, out ALUInstFactory? factory)) throw new Exception("Invalid ALU operation:" + op);
                return factory(ParseOpParam(token[1]), ParseOpParam(token[2]), ParseOpParam(token[3]));
            }
            else if (name.StartsWith("mv"))
            {
                if (token.Length != 3) throw new Exception("Invalid mv instruction");
                IOpParam dst = ParseOpParam(token[1]), src1 = ParseOpParam(token[2]);
                return (dst, src1) switch
                {
                    (RegOpParam p1, ImmOpParam p2) => new AsmInstMvOptRI(p1.regid, p2.imm),
                    _ => new AsmInstMv(dst, src1)
                };
            }
            else if (name.StartsWith("b"))
            {
                if (token.Length != 4) throw new Exception("Invalid branch instruction");
                string op = name.Substring(1);
                if (!brInst.TryGetValue(op, out BRUInstFactory? factory)) throw new Exception("Invalid BRU operation:" + op);
                if (!labelTable.TryGetValue(token[3], out int target)) throw new Exception("Undefined label:" + token[3]);
                IOpParam src1 = ParseOpParam(token[1]), src2 = ParseOpParam(token[2]);
                return (src1, src2) switch
                {
                    (RegOpParam p1, RegOpParam p2) => brInstOptRR[op](p1, p2, target),
                    (RegOpParam p1, ImmOpParam p2) => brInstOptRI[op](p1, p2, target),
                    (ImmOpParam p1, RegOpParam p2) => brInstOptRI[op](p2, p1, target),
                    _ => factory(src1, src2, target)
                };
            }
            else if (name.StartsWith("j"))
            {
                if (token.Length != 2) throw new Exception("Invalid jump instruction");
                if (regidmap.ContainsKey(token[1]))
                {
                    // indirect jump
                    return new AsmInstJr(ParseOpParam(token[1]));
                }
                // direct jump
                if (!labelTable.TryGetValue(token[1], out int target)) throw new Exception("Undefined label:" + token[1]);
                return new AsmInstJ(target);
            }
            else if (name.StartsWith("apc"))
            {
                if (token.Length != 3) throw new Exception("Invalid apc instruction");
                return new AsmInstApc(ParseOpParam(token[1]), ParseOpParam(token[2]));
            }
            else if (name.StartsWith("push"))
            {
                if (token.Length == 1) throw new Exception("Invalid push instruction");
                List<IOpParam> ops = [];
                for (int i = 1; i < token.Length; i++) ops.Add(ParseOpParam(token[i]));

                return new AsmInstPush(ops);
            }
            else if (name.StartsWith("pop"))
            {
                if (token.Length == 1) throw new Exception("Invalid pop instruction");
                List<IOpParam> ops = [];
                for (int i = token.Length - 1; i >= 1; i--) ops.Add(ParseOpParam(token[i]));
                return new AsmInstPop(ops);
            }
            else if (name.StartsWith("in"))
            {
                if (token.Length < 3) throw new Exception("Invalid in instruction");
                var port = ParseOpParam(token[2]);
                if (port is not ImmOpParam ioid) throw new Exception("Invalid port operand(it must be const) :" + token[2]);
                if (token.Length == 3) return new AsmInstIn(ParseOpParam(token[1]), new IOOpParam(ioid.imm), new ImmOpParam(0));
                return new AsmInstIn(ParseOpParam(token[1]), ParseOpParam(token[2]), ParseOpParam(token[3]));
            }
            else if (name.StartsWith("out"))
            {
                if (token.Length < 3) throw new Exception("Invalid out instruction");
                var port = ParseOpParam(token[1]);
                if (port is not ImmOpParam ioid) throw new Exception("Invalid port operand(it must be const) :" + token[1]);
                if (token.Length == 3) return new AsmInstOut(new IOOpParam(ioid.imm), ParseOpParam(token[2]), new ImmOpParam(0));
                return new AsmInstOut(ParseOpParam(token[1]), ParseOpParam(token[2]), ParseOpParam(token[3]));
            }
            else if (name.StartsWith("sync"))
            {
                if (token.Length != 1) throw new Exception("Invalid sync instruction");
                return new AsmInstSync();
            }
            throw new Exception("Invalid instruction:" + inst);
        }

        public void RemoveComments(ref string[] program)
        {
            List<string> before = [];
            for (int i = 0; i < program.Length; i++)
            {
                string t = program[i].Split(';')[0].Trim();
                if (!string.IsNullOrEmpty(t)) before.Add(t);
            }
            program = [.. before];
        }

        public void ScanLable(in string[] program)
        {
            int numInsts = 0;
            for (int i = 0; i < program.Length; i++)
            {
                ref string lable = ref program[i];
                if (lable.EndsWith(":"))
                {
                    // remove ":"
                    string label = lable.Substring(0, lable.Length - 1);
                    if (label.Contains(" ")) throw new Exception("Invalid label:" + label);
                    labelTable[label] = numInsts;
                }
                else numInsts++;
            }
        }
    }

    interface IOpParam : ISaveable
    {
        RegVal Get(in PSASMContext context);
        void Set(in PSASMContext context, RegVal value);
    }

    class RegOpParam(uint regid) : IOpParam
    {
        public uint regid = regid;
        public RegVal Get(in PSASMContext context) => context.rf[regid];
        public void Set(in PSASMContext context, RegVal value) => context.rf[regid] = value;

        public void Store(in List<uint> lst)
        {
            if (regid >= 8) throw new Exception("Save error! Invalid register id:" + regid);
            lst.Add(regid);
        }
        public void Load(in IEnumerator<uint> it)
        {
            regid = it.Current; it.MoveNext();
            if (regid >= 8) throw new Exception("Load error! Invalid register id: " + regid + ", mabe a broken serialized data");
        }
    }

    class ImmOpParam(RegVal imm) : IOpParam
    {
        public RegVal imm = imm;
        public RegVal Get(in PSASMContext context) => imm;
        public void Set(in PSASMContext context, RegVal value) { throw new Exception("Cannot set value of immediate operand"); }
        public void Store(in List<uint> lst)
        {
            lst.Add((uint)imm);
        }
        public void Load(in IEnumerator<uint> it)
        {
            imm = (int)it.Current; it.MoveNext();
        }
    }

    class MemOpParam(IOpParam aop) : IOpParam, ISaveable
    {
        IOpParam aop = aop;
        public RegVal Get(in PSASMContext context)
        {
            uint addr = (uint)aop.Get(context);
            if (addr < context.ram.Length) return context.ram[addr];
            throw new Exception("Invalid memory read: " + (int)addr);
        }
        public void Set(in PSASMContext context, RegVal value)
        {
            uint addr = (uint)aop.Get(context);
            if (addr < context.ram.Length) context.ram[addr] = value;
            throw new Exception("Invalid memory write: " + (int)addr);
        }
        public void Store(in List<uint> lst)
        {
            AsmSerializer.SerializeOne(lst, aop);
        }
        public void Load(in IEnumerator<uint> it)
        {
            aop = AsmSerializer.DeserializeOne(it) as IOpParam ?? throw new Exception("Invalid aop operand, may be a broken serialized data");
        }
    }

    class IOOpParam(int portid) : IOpParam
    {
        int portid = portid;// no used
        public RegVal Get(in PSASMContext context) => context.input;
        public void Set(in PSASMContext context, RegVal value) => context.output = value;

        public void Store(in List<uint> lst)
        {
            lst.Add((uint)portid);
        }
        public void Load(in IEnumerator<uint> it)
        {
            portid = (int)it.Current; it.MoveNext();
            if (portid != 0) throw new Exception("Invalid portid: " + portid + ", may be a broken serialized data");
        }
    }

    public interface IAsmInst
    {
        void Execute(in PSASMContext context);
    }

    class AsmInstArith(in IOpParam dst, in IOpParam src1, in IOpParam src2) : ISaveable
    {
        protected IOpParam dst = dst, src1 = src1, src2 = src2;

        public void Store(in List<uint> lst)
        {
            AsmSerializer.SerializeOne(lst, dst);
            AsmSerializer.SerializeOne(lst, src1);
            AsmSerializer.SerializeOne(lst, src2);
        }
        public void Load(in IEnumerator<uint> it)
        {
            dst = AsmSerializer.DeserializeOne(it) as IOpParam ?? throw new Exception("Invalid dst operand, may be a broken serialized data");
            src1 = AsmSerializer.DeserializeOne(it) as IOpParam ?? throw new Exception("Invalid src1 operand, may be a broken serialized data");
            src2 = AsmSerializer.DeserializeOne(it) as IOpParam ?? throw new Exception("Invalid src2 operand, may be a broken serialized data");
        }
    }

    class AsmInstAdd(in IOpParam dst, in IOpParam src1, in IOpParam src2) : AsmInstArith(dst, src1, src2), IAsmInst
    {

        public void Execute(in PSASMContext context) => dst.Set(context, src1.Get(context) + src2.Get(context));
    }

    class AsmInstAddOptRRI(uint rdidx, uint rs1idx, RegVal imm) : IAsmInst, ISaveable
    {
        uint rdidx = rdidx, rs1idx = rs1idx;
        RegVal imm = imm;
        public void Execute(in PSASMContext context) => context.rf[rdidx] = context.rf[rs1idx] + imm;

        public void Store(in List<uint> lst)
        {
            lst.Add(rdidx);
            lst.Add(rs1idx);
            lst.Add((uint)imm);
        }
        public void Load(in IEnumerator<uint> it)
        {
            rdidx = it.Current; it.MoveNext();
            rs1idx = it.Current; it.MoveNext();
            imm = (int)it.Current; it.MoveNext();
        }
    }

    class AsmInstSub(in IOpParam dst, in IOpParam src1, in IOpParam src2) : AsmInstArith(dst, src1, src2), IAsmInst
    {
        public void Execute(in PSASMContext context) => dst.Set(context, src1.Get(context) - src2.Get(context));
    }

    class AsmInstAnd(in IOpParam dst, in IOpParam src1, in IOpParam src2) : AsmInstArith(dst, src1, src2), IAsmInst
    {
        public void Execute(in PSASMContext context) => dst.Set(context, src1.Get(context) & src2.Get(context));
    }

    class AsmInstOr(in IOpParam dst, in IOpParam src1, in IOpParam src2) : AsmInstArith(dst, src1, src2), IAsmInst
    {
        public void Execute(in PSASMContext context) => dst.Set(context, src1.Get(context) | src2.Get(context));
    }

    class AsmInstXor(in IOpParam dst, in IOpParam src1, in IOpParam src2) : AsmInstArith(dst, src1, src2), IAsmInst
    {
        public void Execute(in PSASMContext context) => dst.Set(context, src1.Get(context) ^ src2.Get(context));
    }

    class AsmInstSll(in IOpParam dst, in IOpParam src1, in IOpParam src2) : AsmInstArith(dst, src1, src2), IAsmInst
    {
        public void Execute(in PSASMContext context) => dst.Set(context, src1.Get(context) << src2.Get(context));
    }

    class AsmInstSrl(in IOpParam dst, in IOpParam src1, in IOpParam src2) : AsmInstArith(dst, src1, src2), IAsmInst
    {
        public void Execute(in PSASMContext context) => dst.Set(context, src1.Get(context) >>> src2.Get(context));
    }

    class AsmInstSra(in IOpParam dst, in IOpParam src1, in IOpParam src2) : AsmInstArith(dst, src1, src2), IAsmInst
    {
        public void Execute(in PSASMContext context) => dst.Set(context, src1.Get(context) >> src2.Get(context));
    }

    class AsmInstEq(in IOpParam dst, in IOpParam src1, in IOpParam src2) : AsmInstArith(dst, src1, src2), IAsmInst
    {
        public void Execute(in PSASMContext context) => dst.Set(context, src1.Get(context) == src2.Get(context) ? 1 : 0);
    }

    class AsmInstNe(in IOpParam dst, in IOpParam src1, in IOpParam src2) : AsmInstArith(dst, src1, src2), IAsmInst
    {
        public void Execute(in PSASMContext context) => dst.Set(context, src1.Get(context) != src2.Get(context) ? 1 : 0);
    }

    class AsmInstLt(in IOpParam dst, in IOpParam src1, in IOpParam src2) : AsmInstArith(dst, src1, src2), IAsmInst
    {
        public void Execute(in PSASMContext context) => dst.Set(context, src1.Get(context) < src2.Get(context) ? 1 : 0);
    }

    class AsmInstGte(in IOpParam dst, in IOpParam src1, in IOpParam src2) : AsmInstArith(dst, src1, src2), IAsmInst
    {
        public void Execute(in PSASMContext context) => dst.Set(context, src1.Get(context) >= src2.Get(context) ? 1 : 0);
    }

    class AsmInstPush(List<IOpParam> srcs) : IAsmInst, ISaveable
    {
        IOpParam[] srcs = [.. srcs];
        public void Execute(in PSASMContext context)
        {
            ref int sp = ref context.rf[(RegVal)AsmParser.RegId.sp];
            for (int i = 0; i < srcs.Length; i++)
            {
                if ((uint)sp < context.ram.Length)
                {
                    context.ram[sp] = srcs[i].Get(context);
                    sp--; // stack pointer decrement
                }
                else throw new Exception("Push stack overflow");
            }
        }

        public void Store(in List<uint> lst)
        {
            lst.Add((uint)srcs.Length);
            foreach (var src in srcs) AsmSerializer.SerializeOne(lst, src);
        }

        public void Load(in IEnumerator<uint> it)
        {
            int len = (int)it.Current; it.MoveNext();
            srcs = new IOpParam[len];
            for (int i = 0; i < len; i++)
            {
                srcs[i] = AsmSerializer.DeserializeOne(it) as IOpParam ?? throw new Exception("Invalid src operand, may be a broken serialized data");
            }
        }

    }

    class AsmInstPop(List<IOpParam> dsts) : IAsmInst, ISaveable
    {
        IOpParam[] dsts = [.. dsts];//NOTE: must be reverse
        public void Execute(in PSASMContext context)
        {
            ref int sp = ref context.rf[(RegVal)AsmParser.RegId.sp];
            for (int i = 0; i < dsts.Length; i++)
            {
                sp++;
                if ((uint)sp < context.ram.Length)
                {
                    dsts[i].Set(context, context.ram[sp]);
                }
                else throw new Exception("Pop stack underflow");
            }
        }

        public void Store(in List<uint> lst)
        {
            lst.Add((uint)dsts.Length);
            foreach (var dst in dsts) AsmSerializer.SerializeOne(lst, dst);
        }

        public void Load(in IEnumerator<uint> it)
        {
            int len = (int)it.Current; it.MoveNext();
            dsts = new IOpParam[len];
            for (int i = 0; i < len; i++)
            {
                dsts[i] = AsmSerializer.DeserializeOne(it) as IOpParam ?? throw new Exception("Invalid dst operand, may be a broken serialized data");
            }
        }
    }

    class AsmInstMv(in IOpParam dst, in IOpParam src1) : IAsmInst, ISaveable
    {
        IOpParam dst = dst, src1 = src1;
        public void Execute(in PSASMContext context) => dst.Set(context, src1.Get(context));

        public void Store(in List<uint> lst)
        {
            AsmSerializer.SerializeOne(lst, dst);
            AsmSerializer.SerializeOne(lst, src1);
        }

        public void Load(in IEnumerator<uint> it)
        {
            dst = AsmSerializer.DeserializeOne(it) as IOpParam ?? throw new Exception("Invalid dst operand, may be a broken serialized data");
            src1 = AsmSerializer.DeserializeOne(it) as IOpParam ?? throw new Exception("Invalid src1 operand, may be a broken serialized data");
        }
    }

    class AsmInstMvOptRI(uint rdidx, RegVal imm) : IAsmInst, ISaveable
    {
        uint rdidx = rdidx;
        RegVal imm = imm;
        public void Execute(in PSASMContext context) => context.rf[rdidx] = imm; // omit twice virtual call

        public void Store(in List<uint> lst)
        {
            lst.Add(rdidx);
            lst.Add((uint)imm);
        }

        public void Load(in IEnumerator<uint> it)
        {
            rdidx = it.Current; it.MoveNext();
            if (rdidx >= 8) throw new Exception("Load error! Invalid register id: " + rdidx + ", mabe a broken serialized data");
            imm = (int)it.Current; it.MoveNext();
        }
    }

    class AsmInstApc(IOpParam dst, IOpParam offset) : IAsmInst, ISaveable
    {
        IOpParam dst = dst;
        IOpParam offset = offset;
        public void Execute(in PSASMContext context) => dst.Set(context, context.pc + offset.Get(context));

        public void Store(in List<uint> lst)
        {
            AsmSerializer.SerializeOne(lst, dst);
            AsmSerializer.SerializeOne(lst, offset);
        }

        public void Load(in IEnumerator<uint> it)
        {
            dst = AsmSerializer.DeserializeOne(it) as IOpParam ?? throw new Exception("Invalid dst operand, may be a broken serialized data");
            offset = AsmSerializer.DeserializeOne(it) as IOpParam ?? throw new Exception("Invalid offset operand, may be a broken serialized data");
        }
    }

    class AsmInstBJ(int target) { protected int target = target - 1; }

    class AsmInstJr(IOpParam src1) : IAsmInst, ISaveable
    {
        IOpParam src1 = src1;
        public void Execute(in PSASMContext context) => context.pc = src1.Get(context) - 1;

        public void Store(in List<uint> lst)
        {
            AsmSerializer.SerializeOne(lst, src1);
        }

        public void Load(in IEnumerator<uint> it)
        {
            src1 = AsmSerializer.DeserializeOne(it) as IOpParam ?? throw new Exception("Invalid src1 operand, may be a broken serialized data");
        }
    }

    class AsmInstJ(int target) : AsmInstBJ(target), IAsmInst, ISaveable
    {
        public void Execute(in PSASMContext context) => context.pc = target;

        public void Store(in List<uint> lst)
        {
            lst.Add((uint)target);
        }

        public void Load(in IEnumerator<uint> it)
        {
            target = (int)it.Current; it.MoveNext();
        }
    }

    class AsmInstBr(in IOpParam src1, in IOpParam src2, int target) : AsmInstBJ(target), ISaveable
    {
        protected IOpParam src1 = src1, src2 = src2;

        public void Store(in List<uint> lst)
        {
            AsmSerializer.SerializeOne(lst, src1);
            AsmSerializer.SerializeOne(lst, src2);
            lst.Add((uint)target);
        }

        public void Load(in IEnumerator<uint> it)
        {
            src1 = AsmSerializer.DeserializeOne(it) as IOpParam ?? throw new Exception("Invalid src1 operand, may be a broken serialized data");
            src2 = AsmSerializer.DeserializeOne(it) as IOpParam ?? throw new Exception("Invalid src2 operand, may be a broken serialized data");
            target = (int)it.Current; it.MoveNext();
        }
    }

    class AsmInstBrOptRR(uint rs1idx, uint rs2idx, int target) : AsmInstBJ(target), ISaveable
    {
        protected uint rs1idx = rs1idx, rs2idx = rs2idx;

        public void Store(in List<uint> lst)
        {
            lst.Add(rs1idx);
            lst.Add(rs2idx);
            lst.Add((uint)target);
        }

        public void Load(in IEnumerator<uint> it)
        {
            rs1idx = it.Current; it.MoveNext();
            if (rs1idx >= 8) throw new Exception("Load error! Invalid register id: " + rs1idx + ", mabe a broken serialized data");
            rs2idx = it.Current; it.MoveNext();
            if (rs2idx >= 8) throw new Exception("Load error! Invalid register id: " + rs2idx + ", mabe a broken serialized data");
            target = (int)it.Current; it.MoveNext();
        }
    }

    class AsmInstBrOptRI(uint rs1idx, RegVal imm, int target) : AsmInstBJ(target), ISaveable
    {
        protected uint rs1idx = rs1idx;
        protected RegVal imm = imm;

        public void Store(in List<uint> lst)
        {
            lst.Add(rs1idx);
            lst.Add((uint)imm);
            lst.Add((uint)target);
        }

        public void Load(in IEnumerator<uint> it)
        {
            rs1idx = it.Current; it.MoveNext();
            if (rs1idx >= 8) throw new Exception("Load error! Invalid register id: " + rs1idx + ", mabe a broken serialized data");
            imm = (int)it.Current; it.MoveNext();
            target = (int)it.Current; it.MoveNext();
        }
    }

    class AsmInstBeq(in IOpParam src1, in IOpParam src2, int target) : AsmInstBr(src1, src2, target), IAsmInst
    {
        public void Execute(in PSASMContext context) { if (src1.Get(context) == src2.Get(context)) context.pc = target; }
    }

    class AsmInstBne(in IOpParam src1, in IOpParam src2, int target) : AsmInstBr(src1, src2, target), IAsmInst
    {
        public void Execute(in PSASMContext context) { if (src1.Get(context) != src2.Get(context)) context.pc = target; }
    }

    class AsmInstBlt(in IOpParam src1, in IOpParam src2, int target) : AsmInstBr(src1, src2, target), IAsmInst
    {
        public void Execute(in PSASMContext context) { if (src1.Get(context) < src2.Get(context)) context.pc = target; }
    }

    class AsmInstBgte(in IOpParam src1, in IOpParam src2, int target) : AsmInstBr(src1, src2, target), IAsmInst
    {
        public void Execute(in PSASMContext context) { if (src1.Get(context) >= src2.Get(context)) context.pc = target; }
    }

    class AsmInstBeqOptRR(uint rs1idx, uint rs2idx, int target) : AsmInstBrOptRR(rs1idx, rs2idx, target), IAsmInst
    {
        public void Execute(in PSASMContext context) { if (context.rf[rs1idx] == context.rf[rs2idx]) context.pc = target; }
    }

    class AsmInstBneOptRR(uint rs1idx, uint rs2idx, int target) : AsmInstBrOptRR(rs1idx, rs2idx, target), IAsmInst
    {
        public void Execute(in PSASMContext context) { if (context.rf[rs1idx] != context.rf[rs2idx]) context.pc = target; }
    }

    class AsmInstBltOptRR(uint rs1idx, uint rs2idx, int target) : AsmInstBrOptRR(rs1idx, rs2idx, target), IAsmInst
    {
        public void Execute(in PSASMContext context) { if (context.rf[rs1idx] < context.rf[rs2idx]) context.pc = target; }
    }

    class AsmInstBgteOptRR(uint rs1idx, uint rs2idx, int target) : AsmInstBrOptRR(rs1idx, rs2idx, target), IAsmInst
    {
        public void Execute(in PSASMContext context) { if (context.rf[rs1idx] >= context.rf[rs2idx]) context.pc = target; }
    }

    class AsmInstBeqOptRI(uint rs1idx, RegVal imm, int target) : AsmInstBrOptRI(rs1idx, imm, target), IAsmInst
    {
        public void Execute(in PSASMContext context) { if (context.rf[rs1idx] == imm) context.pc = target; }
    }

    class AsmInstBneOptRI(uint rs1idx, RegVal imm, int target) : AsmInstBrOptRI(rs1idx, imm, target), IAsmInst
    {
        public void Execute(in PSASMContext context) { if (context.rf[rs1idx] != imm) context.pc = target; }
    }

    class AsmInstBltOptRI(uint rs1idx, RegVal imm, int target) : AsmInstBrOptRI(rs1idx, imm, target), IAsmInst
    {
        public void Execute(in PSASMContext context) { if (context.rf[rs1idx] < imm) context.pc = target; }
    }

    class AsmInstBgteOptRI(uint rs1idx, RegVal imm, int target) : AsmInstBrOptRI(rs1idx, imm, target), IAsmInst
    {
        public void Execute(in PSASMContext context) { if (context.rf[rs1idx] >= imm) context.pc = target; }
    }

    class AsmInstIn(in IOpParam dst, in IOpParam io, in IOpParam offset) : IAsmInst, ISaveable
    {
        protected IOpParam dst = dst, io = io, offset = offset;
        public void Execute(in PSASMContext context) => dst.Set(context, dst.Get(context) | (io.Get(context) << offset.Get(context)));

        public void Store(in List<uint> lst)
        {
            AsmSerializer.SerializeOne(lst, dst);
            AsmSerializer.SerializeOne(lst, io);
            AsmSerializer.SerializeOne(lst, offset);
        }

        public void Load(in IEnumerator<uint> it)
        {
            dst = AsmSerializer.DeserializeOne(it) as IOpParam ?? throw new Exception("Invalid dst operand, may be a broken serialized data");
            io = AsmSerializer.DeserializeOne(it) as IOpParam ?? throw new Exception("Invalid io operand, may be a broken serialized data");
            offset = AsmSerializer.DeserializeOne(it) as IOpParam ?? throw new Exception("Invalid offset operand, may be a broken serialized data");
        }
    }

    class AsmInstOut(in IOpParam io, in IOpParam src1, in IOpParam offset) : IAsmInst, ISaveable
    {
        protected IOpParam io = io, src1 = src1, offset = offset;
        public void Execute(in PSASMContext context) => io.Set(context, src1.Get(context) >> offset.Get(context));

        public void Store(in List<uint> lst)
        {
            AsmSerializer.SerializeOne(lst, io);
            AsmSerializer.SerializeOne(lst, src1);
            AsmSerializer.SerializeOne(lst, offset);
        }

        public void Load(in IEnumerator<uint> it)
        {
            io = AsmSerializer.DeserializeOne(it) as IOpParam ?? throw new Exception("Invalid io operand, may be a broken serialized data");
            src1 = AsmSerializer.DeserializeOne(it) as IOpParam ?? throw new Exception("Invalid src1 operand, may be a broken serialized data");
            offset = AsmSerializer.DeserializeOne(it) as IOpParam ?? throw new Exception("Invalid offset operand, may be a broken serialized data");
        }
    }

    class AsmInstSync : IAsmInst, ISaveable
    {
        public void Execute(in PSASMContext context) { context.sync = true; }
        public void Store(in List<uint> lst) { }
        public void Load(in IEnumerator<uint> it) { }
    }

    class AsmInstNop : IAsmInst, ISaveable
    {
        public void Execute(in PSASMContext context) { }
        public void Store(in List<uint> lst) { }
        public void Load(in IEnumerator<uint> it) { }
    }

    class AsmInstEnd : IAsmInst, ISaveable
    {
        public void Execute(in PSASMContext context) => context.finished = true;
        public void Store(in List<uint> lst) { }
        public void Load(in IEnumerator<uint> it) { }
    }

    delegate IAsmInst ALUInstFactory(IOpParam dst, IOpParam src1, IOpParam src2);
    delegate IAsmInst BRUInstFactory(IOpParam src1, IOpParam src2, int target);

    public interface ISaveable
    {
        void Store(in List<uint> lst);
        void Load(in IEnumerator<uint> it);
    }

    public class AsmSerializer
    {
        readonly static Type[] classes = Assembly.GetExecutingAssembly().GetTypes().Where(t => t.Namespace == "PSASM" && (t.Name.StartsWith("AsmInst") || t.Name.EndsWith("OpParam"))).ToArray();
        readonly static Dictionary<uint, Type> typemapbyhash = classes.ToDictionary(t => JSHash(t.Name), t => t);

        public static Type GetTypeByHash(uint hash)
        {
            if (typemapbyhash.TryGetValue(hash, out Type type))
            {
                return type;
            }
            throw new Exception("Unknown type hash: " + hash);
        }

        public static void SerializeOne(in List<uint> lst, ISaveable obj)
        {
            uint hash = JSHash(obj.GetType().Name);
            lst.Add(hash);
            obj.Store(lst);
        }

        public static ISaveable DeserializeOne(in IEnumerator<uint> it)
        {
            uint hash = it.Current; it.MoveNext();
            Type type = GetTypeByHash(hash);
            ISaveable obj = FormatterServices.GetUninitializedObject(type) as ISaveable ?? throw new Exception("Failed to convert to ISaveable");
            obj.Load(it);
            return obj;
        }

        public static void Serialize(PSASMContext context, out byte[] bytes)
        {
            if (!typemapbyhash.ContainsKey(JSHash("AsmInstAdd"))) throw new Exception("Failed to initialize typemapbyhash");
            List<uint> lst = [];
            context.Store(lst);
            bytes = lst.SelectMany(BitConverter.GetBytes).ToArray();
        }

        public static void Deserialize(in byte[] bytes, in PSASMContext context)
        {
            if (!typemapbyhash.ContainsKey(JSHash("AsmInstAdd"))) throw new Exception("Failed to initialize typemapbyhash");
            uint[] data = new uint[bytes.Length / 4];
            Buffer.BlockCopy(bytes, 0, data, 0, bytes.Length);
            var it = ((IEnumerable<uint>)data).GetEnumerator();
            it.MoveNext();
            context.Load(it);
        }

        public static uint JSHash(string str)
        {
            uint hash = 0;
            for (int i = 0; i < str.Length; i++)
            {
                hash = (hash << 5) + hash + str[i];
            }
            return hash;
        }


    }


}