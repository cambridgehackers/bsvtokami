


typedef struct {
   Bit#(32) f1; 
   Bit#(8) f2;
} StructType;

module mkFoo(Empty);
   Reg#(Bit#(32)) r1 <- mkReg(0);
   rule foorule;
       Bit#(32) v1 = 1;
       Bit#(8) v2 = 8;
       StructType s = StructType { f1: v1, f2: v2 };
   endrule

endmodule
