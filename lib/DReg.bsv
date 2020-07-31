package DReg;

//FIXME
module mkDReg#(a_type dflt_rst_val)(Reg#(a_type)) provisos (Bits#(a_type, sizea));
    Reg#(a_type) r <- mkReg(dflt_rst_val);
    method Action _write(a_type v);
       r <= v;
   endmethod
    method a_type_read();
      return r;
   endmethod
endmodule

//FIXME
module mkDRegU#(a_type dflt_rst_val)(Reg#(a_type)) provisos (Bits#(a_type, sizea));
    Reg#(a_type) r <- mkReg(dflt_rst_val);
    method Action _write(a_type v);
       r <= v;
   endmethod
    method a_type_read();
      return r;
   endmethod
endmodule

//FIXME
module mkDRegA#(a_type dflt_rst_val)(Reg#(a_type)) provisos (Bits#(a_type, sizea));
    Reg#(a_type) r <- mkReg(dflt_rst_val);
    method Action _write(a_type v);
       r <= v;
   endmethod
    method a_type_read();
      return r;
   endmethod
endmodule

endpackage