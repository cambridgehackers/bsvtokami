package FIFO;

interface FIFO#(type element_type);
   method element_type first();
   method Action enq(element_type v);
   method Action deq();
   method Action clear();
endinterface

`ifdef BSVTOKAMI
(* nogen *)
`endif
module mkFIFO(FIFO#(element_type));
endmodule
module mkFIFO1(FIFO#(element_type));
endmodule

endpackage
