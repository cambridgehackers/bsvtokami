package Clocks;

interface Clock;
endinterface

interface Reset;
endinterface

module exposeCurrentClock(Clock);
endmodule

module exposeCurrentReset(Reset);
endmodule

module mkNullCrossingWire #( Clock dClk, a_type dataIn )
                           ( ReadOnly#(a_type) )
   provisos (Bits#(a_type, sa)) ;
endmodule

// C.9.7 FIFO Synchronizers

interface SyncFIFOIfc #(type a_type) ;
   method Action enq ( a_type sendData ) ;
   method Action deq () ;
   method a_type first () ;
   method Bool notFull () ;
   method Bool notEmpty () ;
endinterface

module mkSyncFIFO #( Integer depth,
                     Clock sClkIn, Reset sRstIn,
                     Clock dClkIn )
                   ( SyncFIFOIfc #(a_type) )
   provisos (Bits#(a_type, sa));
endmodule

endpackage
