
module mkMTest(Empty);
    Reg a <- mkReg(0);
    Reg b <- mkReg(0);
    Int x = 0, y = 'h2, z = 19'o33;
    let c = $read(17);
    rule r1;
       a <= a * 3 + x / 22;
       c <= h | a + 3 * d << f;
       b <= -|a;
    endrule
endmodule