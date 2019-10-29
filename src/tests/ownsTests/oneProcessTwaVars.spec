spec oneprocess
p:boolean;
q:boolean;
t:prim_boolean;
process proc{
    owns: p;
	init : global.p && global.q && !own(q) && global.t;
	action setP(){
		frame: p;
		pre: global.p;
		post: !global.p;
	}
    
    action setQ(){
        frame: q;
        pre: global.q && own(global.q);
        post: !global.q;
    }
    
    action getLock(){
        frame:q;
        pre: av(global.q);
        post: own(global.q);
    }
    
	invariant: AG[global.p || !global.p];
}

main(){
 p1:proc;
 run p1();
}

property: AG[global.p || !global.p];