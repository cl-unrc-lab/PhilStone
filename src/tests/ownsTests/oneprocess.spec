spec oneprocess
p:boolean;
process proc{
    owns: p;
	init : global.p;
	action setP(){
		frame: p;
		pre: global.p;
		post: !global.p;
	}
    
    
	invariant: AG[global.p || !global.p];
}

main(){
 p1:proc;
 run p1();
}

property: AG[global.p || !global.p];