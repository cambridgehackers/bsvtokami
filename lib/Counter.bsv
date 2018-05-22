package Counter;

interface Counter#(numeric type sz);
   method Action up();
   method Action down();
   method Action dec(Bit#(sz) v);
   method Action inc(Bit#(sz) v);
   method Action setF(Bit#(sz) v);
   method Action clear();
   method Bit#(sz) value();
endinterface

module mkCounter#(Integer init)(Counter#(sz));
   //FIXME: init
   Reg#(Bit#(sz)) counter <- mkReg(init);
   method Action dec(Bit#(sz) v);
       counter <= counter - v;
   endmethod
   method Action up();
       counter <= counter + 1;
   endmethod
   method Action down();
       counter <= counter - 1;
   endmethod
   method Action inc(Bit#(sz) v);
       counter <= counter + v;
   endmethod
   method Action setF(Bit#(sz) v);
       counter <= v;
   endmethod
   method Action clear();
       counter <= init;
   endmethod
   method Bit#(sz) value();
       return counter;
   endmethod
endmodule

endpackage
