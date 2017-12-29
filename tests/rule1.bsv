
import Foo::*;
export Foo::*;
export Bar(..);

module mkMyTest(Empty);
    rule doDecrementEven if (a == 0 &&& a matches 17);
    	 x <= Valid(a-1);
    endrule
endmodule
