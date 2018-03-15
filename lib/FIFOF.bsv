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

module mkFIFOF(FIFOF#(a));
endmodule

module mkLFIFOF(FIFOF#(a));
endmodule

module mkFIFOF1(FIFOF#(a));
endmodule

module mkUGFIFOF(FIFOF#(element_type))
   provisos (Bits#(element_type, width_any));
endmodule

module mkUGFIFO1(FIFOF#(element_type))
   provisos (Bits#(element_type, width_any));
endmodule

module mkUGSizedFIFOF#(Integer n)(FIFOF#(element_type))
   provisos (Bits#(element_type, width_any));
endmodule

module mkSizedFIFOF#(Integer n)(FIFOF#(element_type))
   provisos (Bits#(element_type, width_any));
endmodule

endpackage
