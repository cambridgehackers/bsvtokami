
module mkInterfaceDef1AsExpression();
    let a = (interface Empty
             endinterface);
endmodule
module mkInterfaceDef2AsExpression();
    let a = (interface Empty;
             endinterface);
endmodule

module mkInterfaceDef3AsExpression();
    let a = (interface Test
                method Action bla(); endmethod
             endinterface);
endmodule

module mkInterfaceDef4AsExpression();
    let a = (interface Test;
                method Action bla(); endmethod
             endinterface);
endmodule


module mkInterfaceDef5AsExpression();
    let a = (interface Test#(4);
                method Action bla(); endmethod
             endinterface:Test);
endmodule


module mkInterfaceDef5AsExpression();
    let a = (interface Test#(4);
    	    let a =1;
	    a=0;
            method Action bla(); endmethod
             endinterface:Test);
endmodule