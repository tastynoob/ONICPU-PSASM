﻿namespace ONICPU
{
    public class FCPU8Config : FCPU4Config
    {
        public new const string ID = "FCPU8";

        protected override string GetID()
        {
            return ID;
        }
        protected override string GetAnim()
        {
            return "fcpu8_kanim";
        }
        protected override int GetH()
        {
            return 8;
        }
        protected override void OnFCpuAdded(FCPU component)
        {
            component.portCount = 8;
            component.CPUType = FCPU.FCPUType.AssemblyCode;
        }
    }
}
