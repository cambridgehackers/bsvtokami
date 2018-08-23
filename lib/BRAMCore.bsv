package BRAMCore;

interface BRAM_PORT#(type addr, type data);
   method Action put(Bool write, addr address, data datain);
   method data   read();
endinterface: BRAM_PORT
interface BRAM_DUAL_PORT#(type addr, type data);
   interface BRAM_PORT#(addr, data) a;
   interface BRAM_PORT#(addr, data) b;
endinterface

(* always_ready *)
interface BRAM_PORT_BE#(type addr, type data, numeric type n);
   method Action put(Bit#(n) writeen, addr address, data datain);
   method data   read();
endinterface: BRAM_PORT_BE
interface BRAM_DUAL_PORT_BE#(type addr, type data, numeric type n);
   interface BRAM_PORT_BE#(addr, data, n) a;
   interface BRAM_PORT_BE#(addr, data, n) b;
endinterface

module mkBRAMCore1#(Integer memSize,
               Bool hasOutputRegister)
               (BRAM_PORT#(addr, data))
   provisos(Bits#(addr, addr_sz), Bits#(data, data_sz));
   Reg#(data) d <- mkRegU();
   method Action put(Bool write, addr address, data datain);
       if (write) begin
	     d <= datain;
	  end
   endmethod
   method data   read();
      return d;
   endmethod
endmodule

(* nogen *)
module mkBRAMCore1BE#(Integer memSize,
                  Bool hasOutputRegister )
                 (BRAM_PORT_BE#(addr, data, n))
   provisos(Bits#(addr, addr_sz), Bits#(data, data_sz),
            Div#(data_sz, n, chunk_sz),
            Mul#(chunk_sz, n, data_sz));
   Reg#(data) d <- mkRegU();
   method Action put(Bit#(n) writeen, addr address, data datain);
      if (writeen != 0) begin
	 d <= datain;
      end
   endmethod
   method data   read();
      return d;
   endmethod
endmodule

(* nogen *)
module mkBRAMCore1Load#(Integer memSize,
                        Bool hasOutputRegister,
                        String file, Bool binary )
                       (BRAM_PORT#(addr, data))
   provisos(Bits#(addr, addr_sz), Bits#(data, data_sz) );
   Reg#(data) d <- mkRegU();
   method Action put(Bool write, addr address, data datain);
       if (write) begin
	  d <= datain;
       end
   endmethod
   method data   read();
      return d;
   endmethod
endmodule

(* nogen *)
module mkBRAMCore1BELoad#(Integer memSize,
                          Bool hasOutputRegister,
                          String file, Bool binary)
                         (BRAM_PORT_BE#(addr, data, n))
   provisos(Bits#(addr, addr_sz), Bits#(data, data_sz),
            Div#(data_sz, n, chunk_sz),
            Mul#(chunk_sz, n, data_sz) );
   Reg#(data) d <- mkRegU();
   method Action put(Bit#(n) writeen, addr address, data datain);
      if (writeen != 0) begin
	 d <= datain;
      end
   endmethod
   method data   read();
      return d;
   endmethod
endmodule

(* nogen *)
module mkBRAMCore2#(Integer memSize,
                    Bool hasOutputRegister )
                   (BRAM_DUAL_PORT#(addr, data))
   provisos(Bits#(addr, addr_sz), Bits#(data, data_sz) );
   Reg#(data) d <- mkRegU();
   interface BRAM_PORT_BE a;
      method Action put(Bool write, addr address, data datain);
	 if (write) begin
	    d <= datain;
	 end
      endmethod
      method data   read();
	 return d;
      endmethod
   endinterface
   interface BRAM_PORT_BE b;
      method Action put(Bool write, addr address, data datain);
	 if (write) begin
	    d <= datain;
	 end
      endmethod
      method data   read();
	 return d;
      endmethod
   endinterface
endmodule

(* nogen *)
module mkBRAMCore2BE#(Integer memSize,
                      Bool hasOutputRegister
                     ) (BRAM_DUAL_PORT_BE#(addr, data, n))
   provisos(Bits#(addr, addr_sz),
            Bits#(data, data_sz),
            Div#(data_sz, n, chunk_sz),
            Mul#(chunk_sz, n, data_sz) );
   Reg#(data) d <- mkRegU();
   interface BRAM_PORT_BE a;
      method Action put(Bit#(n) writeen, addr address, data datain);
	 if (writeen != 0) begin
	    d <= datain;
	 end
      endmethod
      method data   read();
	 return d;
      endmethod
   endinterface
   interface BRAM_PORT_BE b;
      method Action put(Bit#(n) writeen, addr address, data datain);
	 if (writeen != 0) begin
	    d <= datain;
	 end
      endmethod
      method data   read();
	 return d;
      endmethod
   endinterface
endmodule

(* nogen *)
module mkSyncBRAMCore2#(Integer memSize,
                    Bool hasOutputRegister,
                    Clock clkA, Reset rstNA,
                    Clock clkB, Reset rstNB )
                    (BRAM_DUAL_PORT#(addr, data))
   provisos(Bits#(addr, addr_sz),Bits#(data, data_sz));
   Reg#(data) d <- mkRegU();
   interface BRAM_PORT_BE a;
      method Action put(Bool write, addr address, data datain);
	 if (write) begin
	    d <= datain;
	 end
      endmethod
      method data   read();
	 return d;
      endmethod
   endinterface
   interface BRAM_PORT_BE b;
      method Action put(Bool write, addr address, data datain);
	 if (write) begin
	    d <= datain;
	 end
      endmethod
      method data   read();
	 return d;
      endmethod
   endinterface
endmodule

(* nogen *)
module mkSyncBRAMCore2BE#(Integer memSize,
                          Bool hasOutputRegister,
                          Clock clkA, Reset rstNA,
                          Clock clkB, Reset rstNB)
                       (BRAM_DUAL_PORT_BE#(addr, data, n))
   provisos(Bits#(addr, addr_sz),
            Bits#(data, data_sz),
            Div#(data_sz, n, chunk_sz),
            Mul#(chunk_sz, n, data_sz) );
   Reg#(data) d <- mkRegU();
   interface BRAM_PORT_BE a;
      method Action put(Bit#(n) writeen, addr address, data datain);
	 if (writeen != 0) begin
	    d <= datain;
	 end
      endmethod
      method data   read();
	 return d;
      endmethod
   endinterface
   interface BRAM_PORT_BE b;
      method Action put(Bit#(n) writeen, addr address, data datain);
	 if (writeen != 0) begin
	    d <= datain;
	 end
      endmethod
      method data   read();
	 return d;
      endmethod
   endinterface
endmodule

(* nogen *)
module mkBRAMCore2Load#(Integer memSize,
                        Bool hasOutputRegister,
                        String file, Bool binary)
                       (BRAM_DUAL_PORT#(addr, data))
   provisos(Bits#(addr, addr_sz),Bits#(data, data_sz));
   Reg#(data) d <- mkRegU();
   interface BRAM_PORT_BE a;
      method Action put(Bool write, addr address, data datain);
	 if (write) begin
	    d <= datain;
	 end
      endmethod
      method data   read();
	 return d;
      endmethod
   endinterface
   interface BRAM_PORT_BE b;
      method Action put(Bool write, addr address, data datain);
	 if (write) begin
	    d <= datain;
	 end
      endmethod
      method data   read();
	 return d;
      endmethod
   endinterface
   
endmodule

(* nogen *)
module mkBRAMCore2BELoad#(Integer memSize,
                          Bool hasOutputRegister,
                          String file, Bool binary )
                    (BRAM_DUAL_PORT_BE#(addr, data, n))
   provisos(Bits#(addr, addr_sz),
            Bits#(data, data_sz),
            Div#(data_sz, n, chunk_sz),
            Mul#(chunk_sz, n, data_sz) );
   Reg#(data) d <- mkRegU();
   interface BRAM_PORT_BE a;
      method Action put(Bit#(n) writeen, addr address, data datain);
	 if (writeen != 0) begin
	    d <= datain;
	 end
      endmethod
      method data   read();
	 return d;
      endmethod
   endinterface
   interface BRAM_PORT_BE b;
      method Action put(Bit#(n) writeen, addr address, data datain);
	 if (writeen != 0) begin
	    d <= datain;
	 end
      endmethod
      method data   read();
	 return d;
      endmethod
   endinterface
endmodule

(* nogen *)
module mkSyncBRAMCore2Load#(Integer memSize,
                        Bool hasOutputRegister,
                        Clock clkA, Reset rstNA,
                        Clock clkB, Reset rstNB,
                        String file, Bool binary)
                        (BRAM_DUAL_PORT#(addr, data))
   provisos(Bits#(addr, addr_sz), Bits#(data, data_sz));
   Reg#(data) d <- mkRegU();
   interface BRAM_PORT_BE a;
      method Action put(Bool write, addr address, data datain);
	 if (write) begin
	    d <= datain;
	 end
      endmethod
      method data   read();
	 return d;
      endmethod
   endinterface
   interface BRAM_PORT_BE b;
      method Action put(Bool write, addr address, data datain);
	 if (write) begin
	    d <= datain;
	 end
      endmethod
      method data   read();
	 return d;
      endmethod
   endinterface
endmodule

(* nogen *)
module mkSyncBRAMCore2BELoad#(Integer memSize,
                              Bool hasOutputRegister,
                              Clock clkA, Reset rstNA,
                              Clock clkB, Reset rstNB,
                              String file, Bool binary)
                       (BRAM_DUAL_PORT_BE#(addr, data, n))
   provisos(Bits#(addr, addr_sz),
            Bits#(data, data_sz),
            Div#(data_sz, n, chunk_sz),
            Mul#(chunk_sz, n, data_sz) );
   Reg#(data) d <- mkRegU();
   interface BRAM_PORT_BE a;
      method Action put(Bit#(n) writeen, addr address, data datain);
	 if (writeen != 0) begin
	    d <= datain;
	 end
      endmethod
      method data   read();
	 return d;
      endmethod
   endinterface
   interface BRAM_PORT_BE b;
      method Action put(Bit#(n) writeen, addr address, data datain);
	 if (writeen != 0) begin
	    d <= datain;
	 end
      endmethod
      method data   read();
	 return d;
      endmethod
   endinterface
endmodule

endpackage
