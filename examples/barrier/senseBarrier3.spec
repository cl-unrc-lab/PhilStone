/*
Specification for sense barrier algorithm described in "Two Algorithms for barrier synchronization"
p1 communicates de barrier with the rest of processes
pxpy, communication of process x with process y
*/
spec senseBarrier

p1, p2p1, p3p1, p4p1: prim_boolean;

process proc1{
    parity:boolean;
    owns: p1;
    init: !this.parity &&  !global.p1 && !global.p2p1 && !global.p3p1; 
    
    action passBarrier0(){
        frame: parity, p1;
        pre:  !this.parity; /*!this.parity;/* && global.p2p1 && global.p3p1;*/
        post: this.parity && global.p1;
    }
    
    action passBarrier1(){
        frame: parity, p1;
        pre: this.parity;/*this.parity; && !global.p2p1 && !global.p3p1;*/
        post: !this.parity && !global.p1;
    }
    
    invariant: AG[EF[this.parity]] && AG[EF[!this.parity]] && AG[!global.p2p1 || !global.p3p1 || EF[global.p1]];
}
process proc2{
   parity,finish:boolean;
   owns:p2p1;
    init: !this.finish && !this.parity && !global.p1 && !global.p2p1; 
    
    action finish0(){
        frame: finish, p2p1;
        pre: !this.finish; /* || this.finish; !this.finish; && !this.parity;*/
        post: this.finish && global.p2p1;
    }
    
    action finish1(){
        frame: finish, p2p1;
        pre: !this.finish;/* || this.finish;!this.finish; && this.parity;*/
        post: this.finish && !global.p2p1;
    }
    
    action passBarrier0(){
        frame: parity, finish;
        pre: this.finish; /* || this.finish;/* !this.parity; && global.p1 && this.finish;*/
        post: this.parity && !this.finish;
    }
    
    action passBarrier1(){
        frame: parity, finish;
        pre: this.parity;/* || !this.parity; && !global.p1 && this.finish;*/
        post: !this.parity && !this.finish;
    }
    
    invariant: AG[EF[this.parity]] && AG[EF[!this.parity]] &&  AG[EF[this.finish]] && AG[EF[!global.p2p1]] && AG[EF[global.p2p1]];
}

process proc3{
   parity,finish:boolean;
   owns:p3p1;
    init: !this.finish && !this.parity && !global.p1 && !global.p3p1; 
    
    action finish0(){
        frame: finish, p3p1;
        pre: !this.finish;/* && !this.parity;*/
        post: this.finish && global.p3p1;
    }
    
    action finish1(){
        frame: finish, p3p1;
        pre: !this.finish;/* || this.finish; && this.parity;*/
        post: this.finish && !global.p3p1;
    }
    
    action passBarrier0(){
        frame: parity, finish;
        pre: this.finish; /* !this.parity; || this.parity; && global.p1 && this.finish;*/
        post: this.parity && !this.finish;
    }
    
    action passBarrier1(){
        frame: parity, finish;
        pre: this.parity; /*&& !global.p1 && this.finish;*/
        post: !this.parity && !this.finish;
    }
    
    invariant: AG[EF[this.parity]] && AG[EF[!this.parity]] && AG[EF[global.p3p1]]  && AG[EF[!global.p3p1]];
}

main(){
        p1:proc1;
        p2:proc2;
        p3:proc3;
        run p1();
        run p2();
        run p3();
}

property:  AG[(!p2.finish || !p3.finish) || ((p1.parity && p2.parity && p3.parity) || (!p1.parity && !p2.parity && !p3.parity))];


