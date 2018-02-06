typedef  union tagged {
    void MyInvalid;
    Bit#(32) MyValid;
} MyMaybeBit32 deriving (Bits, Eq, FShow);

module mkMyTest(Empty);
    Reg#(MyMaybeBit32) x <- mkReg( tagged MyInvalid );
    rule doDecrementEven(x matches tagged MyValid .a &&& a == 0);
    	 x <= Valid(a-1);
    endrule
endmodule

