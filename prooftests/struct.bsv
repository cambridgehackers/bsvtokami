


typedef struct {
   Bit#(32) f1; 
   Bit#(8) f2;
} StructType;

module mkFoo(Empty);
   Reg#(Bit#(32)) r1 <- mkReg(0);

endmodule
