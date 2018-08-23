package FIFOF;

interface FIFOF#(type element_type);
   method element_type first();
   method Action enq(element_type v);
   method Action deq();
   method Bool notEmpty();
   method Bool notFull();
   method Action clear();
endinterface

`ifdef BSVTOKAMI
(* nogen *)
`endif

module mkFIFOF(FIFOF#(element_type));
   Reg#(element_type) v <- mkRegU();
   Reg#(Bit#(1)) valid <- mkReg(0);
   method element_type first() if (valid == 1); 
      return v;
   endmethod
   method Action enq(element_type new_v) if (valid == 0);
      v <= new_v;
      valid <= 1;
   endmethod
   method Action deq() if (valid == 1);
      valid <= 0;
   endmethod
   method Action clear();
      valid <= 0;
   endmethod
   method Bool notEmpty();
      return (valid != 0);
   endmethod
   method Bool notFull();
      return (valid != 1);
   endmethod
endmodule

module mkLFIFOF(FIFOF#(element_type));
   Reg#(element_type) v <- mkRegU();
   Reg#(Bit#(0)) valid <- mkReg(0);
   method element_type first() if (valid == 1); 
      return v;
   endmethod
   method Action enq(element_type new_v) if (valid == 0);
      v <= new_v;
      valid <= 1;
   endmethod
   method Action deq() if (valid == 1);
      valid <= 0;
   endmethod
   method Action clear();
      valid <= 0;
   endmethod
   method Bool notEmpty();
      return (valid != 0);
   endmethod
   method Bool notFull();
      return (valid != 1);
   endmethod
endmodule

module mkFIFOF1(FIFOF#(element_type));
   Reg#(element_type) v <- mkRegU();
   Reg#(Bit#(0)) valid <- mkReg(0);
   method element_type first() if (valid == 1); 
      return v;
   endmethod
   method Action enq(element_type new_v) if (valid == 0);
      v <= new_v;
      valid <= 1;
   endmethod
   method Action deq() if (valid == 1);
      valid <= 0;
   endmethod
   method Action clear();
      valid <= 0;
   endmethod
   method Bool notEmpty();
      return (valid != 0);
   endmethod
   method Bool notFull();
      return (valid != 1);
   endmethod
endmodule

module mkUGFIFOF(FIFOF#(element_type))
   provisos (Bits#(element_type, width_any));
   Reg#(element_type) v <- mkRegU();
   Reg#(Bit#(0)) valid <- mkReg(0);
   method element_type first(); 
      return v;
   endmethod
   method Action enq(element_type new_v);
      v <= new_v;
      valid <= 1;
   endmethod
   method Action deq();
      valid <= 0;
   endmethod
   method Action clear();
      valid <= 0;
   endmethod
   method Bool notEmpty();
      return (valid != 0);
   endmethod
   method Bool notFull();
      return (valid != 1);
   endmethod
endmodule

module mkUGFIFO1(FIFOF#(element_type))
   provisos (Bits#(element_type, width_any));
   Reg#(element_type) v <- mkRegU();
   Reg#(Bit#(0)) valid <- mkReg(0);
   method element_type first(); 
      return v;
   endmethod
   method Action enq(element_type new_v);
      v <= new_v;
      valid <= 1;
   endmethod
   method Action deq();
      valid <= 0;
   endmethod
   method Action clear();
      valid <= 0;
   endmethod
   method Bool notEmpty();
      return (valid != 0);
   endmethod
   method Bool notFull();
      return (valid != 1);
   endmethod
endmodule

module mkUGSizedFIFOF#(Integer n)(FIFOF#(element_type))
   provisos (Bits#(element_type, width_any));
   Reg#(element_type) v <- mkRegU();
   Reg#(Bit#(0)) valid <- mkReg(0);
   method element_type first(); 
      return v;
   endmethod
   method Action enq(element_type new_v);
      v <= new_v;
      valid <= 1;
   endmethod
   method Action deq();
      valid <= 0;
   endmethod
   method Action clear();
      valid <= 0;
   endmethod
   method Bool notEmpty();
      return (valid != 0);
   endmethod
   method Bool notFull();
      return (valid != 1);
   endmethod
endmodule

module mkSizedFIFOF#(Integer n)(FIFOF#(element_type))
   provisos (Bits#(element_type, width_any));
   Reg#(element_type) v <- mkRegU();
   Reg#(Bit#(0)) valid <- mkReg(0);
   method element_type first() if (valid == 1); 
      return v;
   endmethod
   method Action enq(element_type new_v) if (valid == 0);
      v <= new_v;
      valid <= 1;
   endmethod
   method Action deq() if (valid == 1);
      valid <= 0;
   endmethod
   method Action clear();
      valid <= 0;
   endmethod
   method Bool notEmpty();
      return (valid != 0);
   endmethod
   method Bool notFull();
      return (valid != 1);
   endmethod
endmodule

endpackage
