
import FIFO::*;
import RegFile::*;
import ProcMemSpec::*;
import PipelinedProc::*;

module mkDecExec#(RegFile#(Bit#(PgmSz), Bit#(InstrSz)) pgm,
		  Decoder dec,
                  Executer exec,
		  Scoreboard sb,
		  FIFO#(E2W) e2wFifo,
		  ProcRegs rf,
		  Memory mem,
		  ToHost toHost)(Empty);
   Reg#(Bit#(PgmSz)) pc <- mkReg(0);

   rule decexecArith if (dec.isOp(pgm.sub(pc), opArith)
			&& !sb.search1(dec.getSrc1(pgm.sub(pc)))
			&& !sb.search2(dec.getSrc2(pgm.sub(pc)))
			);
      Bit#(InstrSz) inst = pgm.sub(pc);
      Bit#(RegFileSz) src1 = dec.getSrc1(inst);
      Bit#(RegFileSz) src2 = dec.getSrc2(inst);
      Bit#(RegFileSz) dst = dec.getDst(inst);
      OpArithK arithOp = dec.getArithOp(inst);
      Bit#(DataSz) val1 = rf.read1(src1);
      Bit#(DataSz) val2 = rf.read2(src2);
      Bit#(DataSz) execVal = exec.execArith(arithOp, val1, val2);
      void inserted <- sb.insert(dst);
      E2W e2w = E2W { idx: dst, val: execVal };
      void enq <- e2wFifo.enq(e2w);
      pc <= pc + 1;
   endrule

   rule decexecLd if (dec.isOp(pgm.sub(pc), opLd)
			&& !sb.search1(dec.getDst(pgm.sub(pc)))
			);
      Bit#(InstrSz) inst = pgm.sub(pc);
      Bit#(RegFileSz) src1 = dec.getSrc1(inst);
      Bit#(RegFileSz) dst = dec.getDst(inst);
      Bit#(AddrSz) addr = dec.getAddr(inst);
      Bit#(DataSz) val1 = rf.read1(src1);
      MemRq memrq = MemRq { isLoad: 1'b1, addr: addr, data: val1 };
      Bit#(DataSz) ldVal <- mem.doMem(memrq);
      void inserted <- sb.insert(dst);
      E2W e2w = E2W { idx: dst, val: ldVal };
      void enq <- e2wFifo.enq(e2w);
      pc <= pc + 1;
   endrule

   rule decexecSt if (dec.isOp(pgm.sub(pc), opSt));
      Bit#(InstrSz) inst = pgm.sub(pc);
      Bit#(RegFileSz) src1 = dec.getSrc1(inst);
      Bit#(AddrSz) addr = dec.getAddr(inst);
      Bit#(DataSz) val1 = rf.read1(src1);
      MemRq memrq = MemRq { isLoad: 1'b0, addr: addr, data: val1 };
      Bit#(DataSz) unused <- mem.doMem(memrq);
      pc <= pc + 1;
   endrule

   rule decexecToHost if (dec.isOp(pgm.sub(pc), opTh)
			&& !sb.search1(dec.getSrc1(pgm.sub(pc)))
			);
      Bit#(InstrSz) inst = pgm.sub(pc);
      Bit#(RegFileSz) src1 = dec.getSrc1(inst);
      Bit#(DataSz) val1 = rf.read1(src1);
      void unused <- toHost.toHost(val1);
      pc <= pc + 1;
   endrule

endmodule

module mkDecExecSep#(RegFile#(Bit#(PgmSz), Bit#(InstrSz)) pgm,
		     Decoder dec,
		     Executer exec,
		     ToHost toHost)(Empty);
   FIFO#(D2E) d2eFifo <- mkFIFO();
   FIFO#(E2W) e2wFifo <- mkFIFO();
   Memory mem <- mkMemory();
   ProcRegs rf <- mkProcRegs();
   Scoreboard sb <- mkScoreboard();
   Empty decoder <- mkPipelinedDecoder(pgm, dec, d2eFifo);
   Empty executer <- mkPipelinedExecuter(d2eFifo,
                                         e2wFifo,
                                         sb,
                                         exec,
                                         rf,
					 mem,
					 toHost);
endmodule
