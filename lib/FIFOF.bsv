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

endpackage
