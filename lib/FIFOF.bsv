package FIFOF;

interface FIFOF#(type element_type);
   method element_type first();
   method Action enq(element_type v);
   method Action deq();
   method Bool notEmpty();
   method Bool notFull();
   method Action clear();
endinterface

module mkFIFOF(FIFOF#(element_type)) provisos (Bits#(element_type, esz));
   Reg#(element_type) v <- mkRegU();
   Reg#(Bit#(1)) valid <- mkReg(1'd0);
   method element_type first() if (valid == 1'd1); 
      element_type result = v;
      return result;
   endmethod
   method Action enq(element_type new_v) if (valid == 1'd0);
      v <= new_v;
      valid <= 1'd1;
   endmethod
   method Action deq() if (valid == 1'd1);
      valid <= 1'd0;
   endmethod
   method Action clear();
      valid <= 1'd0;
   endmethod
   method Bool notEmpty();
      return (valid != 1'd0);
   endmethod
   method Bool notFull();
      return (valid != 1'd1);
   endmethod
endmodule

module mkLFIFOF(FIFOF#(element_type)) provisos (Bits#(element_type, esz));
   Reg#(element_type) v <- mkRegU();
   Reg#(Bit#(1)) valid <- mkReg(1'd0);
   method element_type first() if (valid == 1'd1); 
      element_type result = v;
      return result;
   endmethod
   method Action enq(element_type new_v) if (valid == 1'd0);
      v <= new_v;
      valid <= 1'd1;
   endmethod
   method Action deq() if (valid == 1'd1);
      valid <= 1'd0;
   endmethod
   method Action clear();
      valid <= 1'd0;
   endmethod
   method Bool notEmpty();
      return (valid != 1'd0);
   endmethod
   method Bool notFull();
      return (valid != 1'd1);
   endmethod
endmodule

module mkFIFOF1(FIFOF#(element_type));
   Reg#(element_type) v <- mkRegU();
   Reg#(Bit#(1)) valid <- mkReg(1'd0);
   method element_type first() if (valid == 1'd1); 
      return v;
   endmethod
   method Action enq(element_type new_v) if (valid == 1'd0);
      v <= new_v;
      valid <= 1'd1;
   endmethod
   method Action deq() if (valid == 1'd1);
      valid <= 1'd0;
   endmethod
   method Action clear();
      valid <= 1'd0;
   endmethod
   method Bool notEmpty();
      return (valid != 1'd0);
   endmethod
   method Bool notFull();
      return (valid != 1'd1);
   endmethod
endmodule

module mkSizedFIFOF#(Integer n)(FIFOF#(element_type));
   Reg#(element_type) v <- mkRegU();
   Reg#(Bit#(1)) valid <- mkReg(1'd0);
   method element_type first() if (valid == 1'd1); 
      return v;
   endmethod
   method Action enq(element_type new_v) if (valid == 1'd0);
      v <= new_v;
      valid <= 1'd1;
   endmethod
   method Action deq() if (valid == 1'd1);
      valid <= 1'd0;
   endmethod
   method Action clear();
      valid <= 1'd0;
   endmethod
   method Bool notEmpty();
      return (valid != 1'd0);
   endmethod
   method Bool notFull();
      return (valid != 1'd1);
   endmethod
endmodule

endpackage
