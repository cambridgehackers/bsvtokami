
import DefaultValue::*;
import FIFO::*;
import ProcMemSpec::*;
import RegFile::*;

interface ProcRegs;
   method Bit#(DataSz) read1(Bit#(RegFileSz) r1);
   method Bit#(DataSz) read2(Bit#(RegFileSz) r2);
   method Action write(Bit#(RegFileSz) r, Bit#(DataSz) val);
endinterface

module mkProcRegs(ProcRegs);
   RegFile#(Bit#(RegFileSz),Bit#(DataSz)) rf <- mkRegFileFull();
   method Bit#(DataSz) read1(Bit#(RegFileSz) r1);
      Bit#(DataSz) val = rf.sub(r1);
      return val;
   endmethod
   method Bit#(DataSz) read2(Bit#(RegFileSz) r2);
      Bit#(DataSz) val = rf.sub(r2);
      return val;
   endmethod
   method Action write(Bit#(RegFileSz) r, Bit#(DataSz) val);
      void written <- rf.upd(r, val);
   endmethod
endmodule

typedef struct {
   OpK op;
   OpArithK arithOp;
   Bit#(RegFileSz) src1;
   Bit#(RegFileSz) src2;
   Bit#(RegFileSz) dst;
   Bit#(AddrSz) addr;
   Bit#(PgmSz) pc;
   } D2E deriving (Bits);

module mkPipelinedDecoder#(RegFile#(Bit#(PgmSz), Bit#(InstrSz)) pgm,
                           Decoder dec,
                           FIFO#(D2E) d2eFifo)(Empty);
   Reg#(Bit#(PgmSz)) pc <- mkReg(16'h0);

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
      void enq <- d2eFifo.enq(decoded);
      pc <= pc + 16'd1;
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

   method Bool search1(Bit#(RegFileSz) sidx) if (True);
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

module mkPipelinedExecuter#(FIFO#(D2E) d2eFifo,
                            FIFO#(E2W) e2wFifo,
                            Scoreboard sb,
                            Executer exec,
                            ProcRegs rf,
			    Memory mem,
			    ToHost toHost)(Empty);
   D2E d2e = d2eFifo.first();
   rule executeArith if (d2e.op == opArith
                         && !sb.search1(d2e.src1)
                         && !sb.search2(d2e.src2)
                        );
      D2E d2e = d2eFifo.first();
      void deq <- d2eFifo.deq();
      Bit#(RegFileSz) src1 = d2e.src1;
      Bit#(RegFileSz) src2 = d2e.src2;
      Bit#(RegFileSz) dst = d2e.dst;
      OpArithK arithOp = d2e.arithOp;
      Bit#(DataSz) val1 = rf.read1(src1);
      Bit#(DataSz) val2 = rf.read2(src2);
      Bit#(DataSz) execVal = exec.execArith(arithOp, val1, val2);
      void upd <- sb.insert(dst);
      E2W e2w = E2W { idx: dst, val: execVal };
      void enq <- e2wFifo.enq(e2w);
   endrule

   rule executeLoad if (d2e.op == opLd
                         && !sb.search1(d2e.src1)
                         && !sb.search2(d2e.dst)
                        );
      D2E d2e = d2eFifo.first();
      void deq <- d2eFifo.deq();
      Bit#(RegFileSz) src1 = d2e.src1;
      Bit#(RegFileSz) dst = d2e.dst;
      Bit#(AddrSz) addr = d2e.addr;
      Bit#(DataSz) val1 = rf.read1(src1);
      MemRq memrq = MemRq { isLoad: 1'b1, addr: addr, data: 32'b0 };
      Bit#(DataSz) ldVal <- mem.doMem(memrq);
      void insert <- sb.insert(dst);
      E2W e2w = E2W { idx: dst, val: ldVal };
      void enq <- e2wFifo.enq(e2w);
   endrule

   rule executeStore if (d2e.op == opSt
                         && !sb.search1(d2e.src1)
                        );
      D2E d2e = d2eFifo.first();
      void deq <- d2eFifo.deq();
      Bit#(RegFileSz) src1 = d2e.src1;
      Bit#(AddrSz) addr = d2e.addr;
      Bit#(DataSz) val1 = rf.read1(src1);
      MemRq memrq = MemRq { isLoad: 1'b0, addr: addr, data: val1 };
      Bit#(DataSz) unused <- mem.doMem(memrq);
   endrule

   rule executeToHost if (d2e.op == opTh
                         && !sb.search1(d2e.src1)
                        );
      D2E d2e = d2eFifo.first();
      void deq <- d2eFifo.deq();
      Bit#(RegFileSz) src1 = d2e.src1;
      Bit#(AddrSz) addr = d2e.addr;
      Bit#(DataSz) val1 = rf.read1(src1);
      void unused <- toHost.toHost(val1);
   endrule

endmodule

module mkPipelinedWriteback#(FIFO#(E2W) e2wFifo,
                             Scoreboard sb,
                             ProcRegs rf)(Empty);
   rule writeback;
      E2W e2w = e2wFifo.first();
      void deq <- e2wFifo.deq();
      Bit#(RegFileSz) idx = e2w.idx;
      Bit#(DataSz) val = e2w.val;
      void written <- rf.write(idx, val);
      void removed <- sb.remove(idx);
   endrule
endmodule

module mkProcImpl#(RegFile#(Bit#(PgmSz), Bit#(InstrSz)) pgm,
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
   Empty writeback <- mkPipelinedWriteback(e2wFifo,
                                           sb,
                                           rf);
endmodule
