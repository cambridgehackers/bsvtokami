package FIFO;

interface FIFO#(type element_type);
   method element_type first();
   method Action enq(element_type v);
   method Action deq();
   method Action clear();
endinterface

module mkFIFO(FIFO#(element_type)) provisos (Bits#(element_type, esz));
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
endmodule
module mkLFIFO(FIFO#(element_type)) provisos (Bits#(element_type, esz));
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
endmodule
module mkFIFO1(FIFO#(element_type));
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
endmodule

module mkSizedFIFO#(Integer n)(FIFO#(element_type));
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
endmodule

endpackage

