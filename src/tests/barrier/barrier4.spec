spec barrier

sa1, ea1, sb1, eb1, sa2, ea2, sb2, eb2, sa3, ea3, sb3, eb3, sa4, ea4, sb4, eb4: prim_boolean;

process proc1{
    owns: sa1, ea1, sb1, eb1;
    init: global.sa1 && !global.ea1 && !global.sb1 && !global.eb1;
    
    action staySA1(){
        frame: sa1;
        pre: global.sa1;
        post: global.sa1;
    }
    
    action stayEA1(){
        frame: ea1;
        pre: global.ea1;
        post: global.ea1;
    }
    
    action staySB1(){
        frame: sb1;
        pre: global.sb1;
        post: global.sb1;
    }
    
    action stayEB1(){
        frame: eb1;
        pre: global.eb1;
        post: global.eb1;
    }
    
    action finishA(){
        frame: sa1, ea1;
        pre: global.sa1 && !global.ea1;
        post: !global.sa1 && global.ea1;
    }
    
    action startB(){
        frame: ea1, sb1;
        pre: global.ea1;
        post: !global.ea1 && global.sb1;
    }

    action finishB(){
        frame: sb1, eb1;
        pre: global.sb1;
        post: !global.sb1 && global.eb1;
    }
    
     action startA(){
        frame: eb1, sa1;
        pre: global.eb1;
        post: !global.eb1 && global.sa1;
    }
    invariant: EF[global.eb1];
}

process proc2{
    owns: sa2, ea2, sb2, eb2;
    init: global.sa2 && !global.ea2 && !global.sb2 && !global.eb2;
    
     action staySA2(){
        frame: sa2;
        pre: global.sa2;
        post: global.sa2;
    }
    
    action stayEA2(){
        frame: ea2;
        pre: global.ea2;
        post: global.ea2;
    }
    
    action staySB2(){
        frame: sb2;
        pre: global.sb2;
        post: global.sb2;
    }
    
    action stayEB2(){
        frame: eb2;
        pre: global.eb2;
        post: global.eb2;
    }
    
    
    action finishA(){
        frame: sa2, ea2;
        pre: global.sa2 && !global.ea2;
        post: !global.sa2 && global.ea2;
    }
    
    action startB(){
        frame: ea2, sb2;
        pre: global.ea2;
        post: !global.ea2 && global.sb2;
    }

    action finishB(){
        frame: sb2, eb2;
        pre: global.sb2;
        post: !global.sb2 && global.eb2;
    }
    
     action startA(){
        frame: eb2, sa2;
        pre: global.eb2;
        post: !global.eb2 && global.sa2;
    }
    invariant: EF[global.eb2];
}

process proc3{
    owns: sa3, ea3, sb3, eb3;
    init: global.sa3 && !global.ea3 && !global.sb3 && !global.eb3;
    
     action staySA3(){
        frame: sa3;
        pre: global.sa3;
        post: global.sa3;
    }
    
    action stayEA3(){
        frame: ea3;
        pre: global.ea3;
        post: global.ea3;
    }
    
    action staySB3(){
        frame: sb3;
        pre: global.sb3;
        post: global.sb3;
    }
    
    action stayEB3(){
        frame: eb3;
        pre: global.eb3;
        post: global.eb3;
    }
    
    
    action finishA(){
        frame: sa3, ea3;
        pre: global.sa3 && !global.ea3;
        post: !global.sa3 && global.ea3;
    }
    
    action startB(){
        frame: ea3, sb3;
        pre: global.ea3;
        post: !global.ea3 && global.sb3;
    }

    action finishB(){
        frame: sb3, eb3;
        pre: global.sb3;
        post: !global.sb3 && global.eb3;
    }
    
     action startA(){
        frame: eb3, sa3;
        pre: global.eb3;
        post: !global.eb3 && global.sa3;
    }
    invariant: EF[global.eb3];
}

process proc4{
    owns: sa4, ea4, sb4, eb4;
    init: global.sa4 && !global.ea4 && !global.sb4 && !global.eb4;
    
     action staySA4(){
        frame: sa4;
        pre: global.sa4;
        post: global.sa4;
    }
    
    action stayEA4(){
        frame: ea4;
        pre: global.ea4;
        post: global.ea4;
    }
    
    action staySB4(){
        frame: sb4;
        pre: global.sb4;
        post: global.sb4;
    }
    
    action stayEB4(){
        frame: eb4;
        pre: global.eb4;
        post: global.eb4;
    }
    
    
    action finishA(){
        frame: sa4, ea4;
        pre: global.sa4 && !global.ea4;
        post: !global.sa4 && global.ea4;
    }
    
    action startB(){
        frame: ea4, sb4;
        pre: global.ea4;
        post: !global.ea4 && global.sb4;
    }

    action finishB(){
        frame: sb4, eb4;
        pre: global.sb4;
        post: !global.sb4 && global.eb4;
    }
    
     action startA(){
        frame: eb4, sa4;
        pre: global.eb4;
        post: !global.eb4 && global.sa4;
    }
    invariant: EF[global.eb4];
}




main(){
        p1:proc1;
        p2:proc2;
        p3:proc3;
        run p1();
        run p2();
        run p3();
}
/*property: AG[!(global.sa1 && global.sb2)];*/
property: AG[!(global.sa1 && global.sb2)];