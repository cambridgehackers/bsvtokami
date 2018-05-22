package FIFOLevel;

interface FIFOLevelIfc#( type element_type, numeric type fifoDepth ) ;
   method Action enq( element_type x1 );
   method Action deq();
   method element_type first();
   method Action clear();
   method Bool notFull ;
   method Bool notEmpty ;
   method Bool isLessThan   ( Integer c1 ) ;
   method Bool isGreaterThan( Integer c1 ) ;
endinterface

(* nogen *)
module mkFIFOLevel (
          FIFOLevelIfc#(element_type, fifoDepth) )
   provisos( Bits#(element_type, width_element ),
             Log#(TAdd#(fifoDepth,1),cntSize) ) ;
endmodule

(* nogen *)
module mkGFIFOLevel#(Bool ugenq, Bool ugdeq, Bool ugcount)
           ( FIFOLevelIfc#(element_type, fifoDepth) )
   provisos( Bits#(element_type, width_element ),
            Log#(TAdd#(fifoDepth,1),cntSize));
endmodule

endpackage
