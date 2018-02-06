typedef struct {
    Bool valid;
    Bit#(32) value;
} MyMaybeBit32 deriving (Bits, Eq, FShow);

module mkMyTest(Empty);
    Reg#(MyMaybeBit32) x <- mkReg( MyMaybeBit32{ valid: False, value: 0 } );
    rule doDecrementEven(x matches tagged MyMaybeBit32{ valid: True, value: .value } &&& value[0] == 0);
        let new_value = value - 1;
        x <= MyMaybeBit32{ valid: (new_value != 0), value: new_value };
    endrule
    rule doDecrementOdd(x.valid && (x.value[0] == 1));
        match tagged MyMaybeBit32{ valid: .valid, value: .value } = x;
        let new_value = value - 1;
        x <= MyMaybeBit32{ valid: (new_value != 0), value: new_value };
    endrule
    rule doReset(x matches tagged MyMaybeBit32{ valid: False, value: .* });
        x <= MyMaybeBit32{ valid: True, value: 42 };
    endrule
endmodule

