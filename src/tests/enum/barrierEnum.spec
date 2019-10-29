spec barrier


primenum state1 = {sa1, ea1, sb1, eb1};
primenum state2 = {sa2, ea2, sb2, eb2};

process proc1{
    owns: state1;
    init: global.state1=sa1 && global.state2=sa2;
    
    action staySA1(){
        frame: state1;
        pre: global.state1=sa1;
        post: global.state1=sa1;
    }
    
    action stayEA1(){
        frame: state1;
        pre: global.state1=ea1;
        post: global.state1=ea1;
    }
    
    action staySB1(){
        frame: state1;
        pre: global.state1=sb1;
        post: global.state1=sb1;
    }
    
    action stayEB1(){
        frame: state1;
        pre: global.state1=se1;
        post: global.state1=se1;
    }
    
    action finishA(){
        frame: state1;
        pre: global.state=sa1;
        post: global.state=ea1;
    }
    
    action startB(){
        frame: state1;
        pre: global.state1=ea1;
        post: global.state1=sb1;
    }

    action finishB(){
        frame: state1;
        pre: global.state1=sb1;
        post: global.state1=eb1;
    }
    
     action startA(){
        frame: state1;
        pre: global.state1=eb1;
        post: global.state1=sa1;
    }
    invariant: AG[global.sa1 || !global.sa1];
}

process proc2{
    owns: state2;
    init: global.state2=sa2 && global.state1=sa1;
    
     action staySA2(){
        frame: state2;
        pre: global.state2=sa2;
        post: global.state2=sa2;
    }
    
    action stayEA2(){
        frame: state2;
        pre: global.state2=ea2;
        post: global.state2=ea2;
    }
    
    action staySB2(){
        frame: state2;
        pre: global.state2=sb2;
        post: global.state2=sb2;
    }
    
    action stayEB2(){
        frame: state2;
        pre: global.state2=se2;
        post: global.state2=se2;
    }
    
    action finishA(){
        frame: state2;
        pre: global.state2=sa2;
        post: global.state2=ea2;
    }
    
    action startB(){
        frame: state2;
        pre: global.state2=ea2;
        post: global.state2=sb2;
    }

    action finishB(){
        frame: state2;
        pre: global.state2=sb2;
        post: global.state2=eb2;
    }
    
     action startA(){
        frame: state2;
        pre: global.state2=eb2;
        post: global.state2=sa2;
    }
    invariant: AG[global.sa1 || !global.sa1];
}

main(){
        p1:proc1;
        p2:proc2;
        run p1();
        run p2();
}
/*property: AG[!(global.state1=sa1 && global.state2=sb2)];*/
property: AG[!global.state1=sa1 || global.state2=sb2];