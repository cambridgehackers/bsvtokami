package RegFile;

interface RegFile #(type index_t, type data_t);
    method Action upd(index_t addr, data_t d);
    method data_t sub(index_t addr);
endinterface: RegFile

module mkRegFile#( index_t lo_index, index_t hi_index )
                 ( RegFile#(index_t, data_t) )
  provisos (Bits#(index_t, size_index),
            Bits#(data_t,  size_data));
endmodule

module mkRegFileFull( RegFile#(index_t, data_t) )
  provisos (Bits#(index_t, size_index),
            Bits#(data_t, size_data),
            Bounded#(index_t) );
endmodule

module mkRegFileWCF#( index_t lo_index, index_t hi_index )
                    ( RegFile#(index_t, data_t) )
  provisos (Bits#(index_t, size_index),
            Bits#(data_t,  size_data));
   
endmodule

module mkRegFileLoad#
           ( String file, index_t lo_index, index_t hi_index)
           ( RegFile#(index_t, data_t) )
  provisos (Bits#(index_t, size_index),
            Bits#(data_t, size_data));
   
endmodule

module mkRegFileFullLoad#( String file)
                         ( RegFile#(index_t, data_t))
  provisos (Bits#(index_t, size_index),
            Bits#(data_t, size_data),
            Bounded#(index_t) );
endmodule

module mkRegFileWCFLoad#
           ( String file, index_t lo_index, index_t hi_index)
           ( RegFile#(index_t, data_t) )
  provisos (Bits#(index_t, size_index),
            Bits#(data_t, size_data));
   
endmodule

endpackage
