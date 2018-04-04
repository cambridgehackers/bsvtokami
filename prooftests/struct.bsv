


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

module mkFoo(Empty);
   Reg#(Bit#(32)) r1 <- mkReg(0);
   rule foorule;
      Bit#(32) v1 = 1;
      Bit#(8) v2 = 8;
      StructType s = StructType { f1: v1, f2: v2 };
      MaybeBit32 mb32 = tagged Valid32 v1;
      FooTaggedUnion ftu1 = tagged T1 { f1: v1, f2: v2 };
      FooTaggedUnion ftu2 = tagged T2 { f1: v1, f2: v2 };
      case (ftu2) matches
	 tagged T2 { f1: .mv1, f2: .mv2 }:
	    r1 <= mv1;
      endcase
   endrule

endmodule
