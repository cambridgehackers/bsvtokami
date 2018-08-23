


typedef struct {
   Bit#(32) f1; 
   Bit#(8) f2;
} StructType;

typedef union tagged {
   Bit#(32) Valid32;
   Bit#(1) Invalid32;
   } MaybeBit32;

typedef union tagged {
   struct { Bit#(32) f1; Bit#(8) f2; } T1;
   struct { Bit#(32) f1; Bit#(8) f2; } T2;
   } FooTaggedUnion;

typedef enum {
   First,
   Second = 10,
   Batch[5],
   Batch[100:109] = 100
   } FooEnum;

module mkFoo(Empty);
   Bit#(32) initval = 0;
   Reg#(Bit#(32)) r1 <- mkReg(initval);
   rule foorule;
      Bit#(32) v1 = 32'd1;
      Bit#(8) v2 = 8'd8;
      StructType s = StructType { f1: v1, f2: v2 };
      MaybeBit32 mb32 = tagged Valid32 v1;
`ifdef MORE_DEBUGGING
      FooTaggedUnion ftu1 = tagged T1 { f1: v1, f2: v2 };
      FooTaggedUnion ftu2 = tagged T2 { f1: v1, f2: v2 };
      case (ftu2) matches
	 tagged T2 { f1: .mv1, f2: .mv2 }: begin
	    r1 <= mv1;
	 end
	 default: begin
         end
      endcase
`endif
   endrule

endmodule
