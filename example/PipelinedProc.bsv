
import DefaultValue::*;
import FIFO::*;
import ProcMemSpec::*;
import RegFile::*;

interface ProcRegs;
   method Bit#(DataSz) read1(Bit#(RegFileSz) r1);
   method Bit#(DataSz) read2(Bit#(RegFileSz) r2);
   method Action write(Bit#(RegFileSz) r, Bit#(DataSz) val);
endinterface

typedef struct {
   OpK op;
   OpArithK arithOp;
   Bit#(RegFileSz) src1;
   Bit#(RegFileSz) src2;
   Bit#(RegFileSz) dst;
   Bit#(AddrSz) addr;
   Bit#(PgmSz) pc;
   } D2E deriving (Bits);

interface PipelinedDecoder;
endinterface

module mkPipelinedDecoder#(Bit#(PgmSz) pcInit,
			   RegFile#(Bit#(PgmSz), Bit#(InstrSz)) pgm,
			   Decoder dec,
			   FIFO#(D2E) d2e)(PipelinedDecoder);
   Reg#(Bit#(PgmSz)) pc <- mkReg(0);
   
   rule decode;
      Bit#(InstrSz) inst = pgm.sub(pc);
      OpK op = dec.getOp(inst);
      OpArithK arithOp = dec.getArithOp(inst);
      Bit#(RegFileSz) src1 = dec.getSrc1(inst);
      Bit#(RegFileSz) src2 = dec.getSrc2(inst);
      Bit#(RegFileSz) dst = dec.getDst(inst);
      Bit#(AddrSz) addr = dec.getAddr(inst);

      D2E decoded = D2E {
	 op: op, arithOp: arithOp, src1: src1, src2: src2, dst: dst, addr: addr, pc: pc
	 };
      d2e.enq(decoded);
      pc <= pc + 1;
   endrule
endmodule

interface Scoreboard;
   method Bool search1(Bit#(RegFileSz) sidx);
   method Bool search2(Bit#(RegFileSz) sidx);
   method Action insert(Bit#(RegFileSz) sidx);
   method Action remove(Bit#(RegFileSz) sidx);
endinterface

module mkScoreboard(Scoreboard);
   RegFile#(Bit#(RegFileSz), Bool) sbFlags <- mkRegFileFull();
   
   method Bool search1(Bit#(RegFileSz) sidx);
      Bool flag = sbFlags.sub(sidx);
      return flag;
   endmethod

   method Bool search2(Bit#(RegFileSz) sidx);
      Bool flag = sbFlags.sub(sidx);
      return flag;
   endmethod

   method Action insert(Bit#(RegFileSz) nidx);
      void unused <- sbFlags.upd(nidx, True);
   endmethod

   method Action remove(Bit#(RegFileSz) nidx);
      void unused <- sbFlags.upd(nidx, False);
   endmethod
endmodule

typedef struct {
   Bit#(RegFileSz) idx;
   Bit#(DataSz) val;
   } E2W deriving(Bits);

module mkExecuter#(FIFO#(D2E) d2eFifo,
		   FIFO#(E2W) e2wFifo,
		   Scoreboard sb,
		   Executer exec,
		   ProcRegs rf)(Empty);
   D2E d2e = d2eFifo.first();
   rule executeArith if (d2e.op == opArith
                         && sb.search1(d2e.src1)
                         && sb.search2(d2e.src2)
			);
      D2E d2e = d2eFifo.first();
      void deq <- d2eFifo.deq();
      Bit#(RegFileSz) src1 = d2e.src1;
      Bit#(RegFileSz) src2 = d2e.src2;
      Bit#(RegFileSz) dst = d2e.dst;
      OpArithK arithOp = d2e.arithOp;
      Bit#(DataSz) val1 = rf.read1(src1);
      Bit#(DataSz) val2 = rf.read1(src2);
      Bit#(DataSz) execVal = exec.execArith(arithOp, val1, val2);
      void upd <- sb.insert(dst);
      E2W e2w = E2W { idx: dst, val: execVal };
      void enq <- e2wFifo.enq(e2w);
   endrule
endmodule
