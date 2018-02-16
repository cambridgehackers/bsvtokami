package ClientServer;

import GetPut::*;
import Connectable::*;

interface Client#(type req_type, type resp_type);
   interface Get#(req_type) request;
   interface Put#(resp_type) response;
endinterface

interface Server#(type req_type, type resp_type);
   interface Put#(req_type) request;
   interface Get#(resp_type) response;
endinterface

instance Connectable#(Client#(req_type, resp_type), Server#(req_type, resp_type))
   provisos(Connectable#(Get#(req_type), Put#(req_type))
	    , Connectable#(Get#(resp_type), Put#(resp_type)));
   module mkConnection#(Client#(req_type, resp_type) c, Server#(req_type, resp_type) s)(Empty);
      mkConnection(c.request, s.request);
      mkConnection(s.response, c.response);
   endmodule
endinstance

instance Connectable#(Server#(req_type, resp_type), Client#(req_type, resp_type))
   provisos(Connectable#(Get#(req_type), Put#(req_type))
	    , Connectable#(Get#(resp_type), Put#(resp_type)));
   module mkConnection#(Server#(req_type, resp_type) s, Client#(req_type, resp_type) c)(Empty);
      mkConnection(c.request, s.request);
      mkConnection(s.response, c.response);
   endmodule
endinstance

endpackage
