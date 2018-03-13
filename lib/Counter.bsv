package Counter;

interface Counter#(numeric type sz);
   method Action dec(Bit#(sz) v);
   method Action inc(Bit#(sz) v);
   method Action setF(Bit#(sz) v);
   method Bit#(sz) value();
endinterface

module mkCounter#(Bit#(sz) init)(Counter#(sz));
endmodule

endpackage
