spec barrier

sa1, ea1, sb1, eb1, sa2, ea2, sb2, eb2: boolean;

process proc1{
    init: global.sa1 && !global.ea1 && !global.sb1 && !global.eb1 && own(global.sa1) && own(global.ea1) && own(global.sb1) && own(global.eb1) && !own(global.sa2) && !own(global.ea2) && !own(global.sb2) && !own(global.eb2);
    
    action finishA(){
        frame: sa1, ea1;
        pre: global.sa1 && !global.ea1 && own(global.sa1) && own(global.ea1);
        post: !global.sa1 && global.ea1 && own(global.sa1) && own(global.ea1);
    }
    
    action startB(){
        frame: ea1, sb1;
        pre: global.ea1 && own(global.sb1) && own(global.ea1);
        post: !global.ea1 && global.sb1 && own(global.sb1) && own(global.ea1);
    }

    action finishB(){
        frame: sb1, eb1;
        pre: global.sb1 && own(global.eb1) && own(global.sb1);
        post: !global.sb1 && global.eb1 && own(global.sb1) && own(global.eb1);
    }
    
     action startA(){
        frame: eb1, sa1;
        pre: global.eb1 && own(global.sa1) && own(global.eb1);
        post: !global.eb1 && global.sa1 && own(global.sa1) && own(global.eb1);
    }
    invariant: AG[own(sa1)] && AG[own(ea1)] && AG[own(sb1)] && AG[own(eb1)];
}

process proc2{
    init: global.sa2 && !global.ea2 && !global.sb2 && !global.eb2 && own(global.sa2) && !own(global.sa1) && !own(global.ea1) && !own(global.sb1) && !own(global.eb1);
    
    action finishA(){
        frame: sa2, ea2;
        pre: global.sa2 && own(global.sa2) && own(global.ea2);
        post: !global.sa2 && global.ea2 && own(global.sa2) && own(global.ea2);
    }
    
    action startB(){
        frame: ea2, sb2;
        pre: global.ea2 && own(global.sb2) && own(global.ea2);
        post: !global.ea2 && global.sb2 && own(global.sb2) && own(global.ea2);
    }

    action finishB(){
        frame: sb2, eb2;
        pre: global.sb2 && own(global.eb2) && own(global.sb2);
        post: !global.sb2 && global.eb2 && own(global.sb2) && own(global.eb2);
    }
    
     action startA(){
        frame: eb2, sa2;
        pre: global.eb2 && own(global.sa2) && own(global.eb2);
        post: !global.eb2 && global.sa2 && own(global.sa2) && own(global.eb2);
    }
    invariant: AG[!(global.sa2 && global.ea2)]&& AG[!(global.sa2&&global.sb2)] && AG[!(global.sa2&&global.eb2)] && AG[!(global.ea2&&global.sb2)] && AG[!(global.ea2 && global.eb2)] && AG[!(global.sb2 && global.eb2)] && AG[!global.ea2 || AX[global.sb2]] && AG[!global.sb2 || AX[global.eb2]] && AG[!global.eb2 || AX[global.sa2]] && EF[global.eb2];
}

main(){
        p1:proc1;
        p2:proc2;
        run p1();
        run p2();
}
property: AG[!(global.sa1 && global.sb2)] && AG[!(global.sa2 && global.sb1)];
