spec barrier

a1,s1,s2,b1,a2,b2: prim_boolean;

process proc1{
    init: global.a1 && global.s1 && !global.b1 && global.s2;
    
    action finishA(){
        frame: s1;
        pre: global.s1;
        post: !global.s1;
    }
    
    action startB(){
        frame: s1, b1,a1;
        pre: !global.s1 ;
        post: !global.a1 && global.b1 && global.s1;
    }

    action finishB(){
        frame: s1;
        pre: global.b1 && global.s1;
        post: !global.s1 ;
    }
    
     action startA(){
        frame: b1, s1, a1;
        pre: global.b1 && !global.s1;
        post: !global.b1 && global.s1 && global.a1;
    }
    invariant: AG[global.a1 || !global.a1];
}

main(){
        p1:proc1;
        run p1();
}
property: AG[!(global.a1 && global.b1)];
