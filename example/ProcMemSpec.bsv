import DefaultValue::*;
import RegFile::*;
import Vector::*;


Bit#(2) opArith = 2'b00;
Bit#(2) opLd = 2'b01;
Bit#(2) opSt = 2'b10;
Bit#(2) opTh = 2'b11;

typedef Bit#(2) OpK;

Bit#(2) opArithAdd = 2'b00;
Bit#(2) opArithSub = 2'b01;
Bit#(2) opArithMul = 2'b10;
Bit#(2) opArithDiv = 2'b11;

typedef Bit#(2) OpArithK;

interface Decoder#(type instK, numeric type rfsz, numeric type addrsz);
   method OpK getOp(instK inst);
   method Bit#(rfsz) getSrc1(instK inst);
   method Bit#(rfsz) getSrc2(instK inst);
   method Bit#(rfsz) getDst(instK inst);
   method Bit#(addrsz) getAddr(instK inst);
endinterface

module mkDecoder(Decoder#(instK, rfsz, addrsz));
endmodule

interface Executer#(type instK, type dataK);
   method dataK execArith(OpArithK op, dataK val1, dataK val2);
endinterface

module mkExecuter(Executer#(instK, dataK));
endmodule

typedef struct {
   Bool isLoad;
   Bit#(addrsz) addr;
   dataK data;
   } MemRq#(numeric type addrsz, type dataK) deriving (Bits);

interface Memory#(numeric type addrsz, type dataK);
   method ActionValue#(dataK) doMem(MemRq#(addrsz, dataK) req);
endinterface

module mkMemory(Memory#(addrsz, dataK)) provisos (Bits#(dataK, datasz));
   RegFile#(Bit#(addrsz), dataK) mem <- mkRegFileFull();
   method ActionValue#(dataK) doMem(MemRq#(addrsz, dataK) req);
      if (req.isLoad) begin
	 let ldval = mem.sub(req.addr);
	 return ldval;
	 end
      else begin
	 mem.upd(req.addr, req.data);
	 return mem.sub(req.addr);
      end
   endmethod
endmodule

interface ToHost#(type dataK);
   method Action toHost(dataK val);
endinterface

typedef struct {
   Bit#(addrsz) pcInit;
   Vector#(rfsz, dataK) rfInit;
   Vector#(pgmsz, instK) pgmInit;
   } ProcInit#(numeric type addrsz, numeric type pgmsz, type instK, numeric type rfsz, type dataK) deriving (Bits);

module procSpec#(ProcInit#(addrsz, pgmsz, instK, rfsz, dataK) procInit, ToHost#(dataK) tohost)(Empty) provisos (Bits#(instK, instsz), Bits#(dataK, datasz));
   Reg#(Bit#(addrsz)) pc <- mkReg(procInit.pcInit);
   RegFile#(Bit#(rfsz), dataK) rf <- mkRegFileFull();
   Memory#(addrsz, dataK) mem <- mkMemory();
   RegFile#(Bit#(addrsz), instK) pgm <- mkRegFile(0, fromInteger(valueOf(pgmsz)));

   Decoder#(instK, rfsz, addrsz) dec <- mkDecoder();
   Executer#(instK, dataK) exec <- mkExecuter();

   instK inst = pgm.sub(pc);

   rule doArith if (dec.getOp(inst) == opArith);
      instK inst = pgm.sub(pc);
      OpK op = dec.getOp(inst);
      Bit#(rfsz) src1 = dec.getSrc1(inst);
      Bit#(rfsz) src2 = dec.getSrc2(inst);
      Bit#(rfsz) dst = dec.getDst(inst);
      dataK val1 = rf.sub(src1);
      dataK val2 = rf.sub(src2);
      dataK dval = exec.execArith(op, val1, val2);
      rf.upd(dst, dval);
      pc <= pc + 1;
   endrule

   rule doLoad if (dec.getOp(inst) == opLd);
      instK inst = pgm.sub(pc);
      Bit#(addrsz) addr = dec.getAddr(inst);
      Bit#(rfsz) dst = dec.getDst(inst);
      dataK val <- mem.doMem(MemRq { isLoad: True, addr: addr, data: defaultValue });
      rf.upd(dst, val);
      pc <= pc + 1;
   endrule

   rule doStore if (dec.getOp(inst) == opSt);
      instK inst = pgm.sub(pc);
      Bit#(addrsz) addr = dec.getAddr(inst);
      Bit#(rfsz) src = dec.getSrc1(inst);
      dataK val = rf.sub(src);
      mem.doMem(MemRq { isLoad: False, addr: addr, data: val });
      pc <= pc + 1;
   endrule

   rule doHost if (dec.getOp(inst) == opTh);
      instK inst = pgm.sub(pc);
      Bit#(rfsz) src1 = dec.getSrc1(inst);
      dataK val1 = rf.sub(src1);
      
      tohost.toHost(val1);
      pc <= pc + 1;

   endrule

endmodule
