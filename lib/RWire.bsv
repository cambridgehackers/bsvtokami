package RWire;

interface RWire#(type element_type) ;
   method Action wset(element_type datain) ;
   method Maybe#(element_type) wget() ;
endinterface: RWire

module mkRWireSBR(RWire#(element_type))
   provisos (Bits#(element_type, element_width)) ;
endmodule

module mkUnsafeRWire(RWire#(element_type))
   provisos (Bits#(element_type, element_width)) ;
endmodule

module mkRWire(RWire#(element_type))
   provisos (Bits#(element_type, element_width)) ;
endmodule

endpackage
