/**
   We represent ASTs using maps (objects) in a generic manner. Each
   object is assumed to have at least the following two fields:
   
   - "op"; which indicates node-type, and
   - "children"; an array of child nodes and their order (empty for terminal nodes)
 
   representation of the statement "y = 42;"

   { op: "statement"
     children: ["assignExp"]
     assignExp: { op: "exp"
            children: ["assign"]
	    assign: {op: "assign"
	             children: ["lval", "assignOp", "exp"]
		     lval: {op: "id", children: [], value: "y"}
		     assignOp: {op "assignOp" value: "="}
		     exp: {op: "exp", children: ["num"] 


   Alternatively, just use the 'treehugger' library for ASTs?
   https://github.com/ajaxorg/treehugger
**/
