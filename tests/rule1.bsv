
import Foo::*;
export Foo::*;
export Bar(..);

module mkMyTest(Empty);
    Reg#(Maybe#(Bit#(12))) x <- mkReg(0);
    Bit#(12) a = 17;
    rule doDecrementEven if (a == x &&& a matches 17);
    	 x <= Valid(a-1);
    endrule
endmodule
