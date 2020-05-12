/*
Specification for sense barrier algorithm described in "Two Algorithms for barrier synchronization"
p1 communicates de barrier with the rest of processes
pxpy, communication of process x with process y
*/
spec senseBarrier

p1, p2p1: prim_boolean;

process proc1{
    parity:boolean;
    owns: p1;
    init: !this.parity &&  !global.p1 && !global.p2p1; 
    
    action passBarrier0(){
        frame: parity, p1;
        pre: !this.parity && global.p2p1;
        post: this.parity && global.p1;
    }
    
    action passBarrier1(){
        frame: parity, p1;
        pre: this.parity && !global.p2p1;
        post: !this.parity && !global.p1;
    }
    
    invariant: AG[EF[this.parity]] && AG[EF[!this.parity]];
}
process proc2{
   parity,finish:boolean;
   owns:p2p1;
    init: !this.finish && !this.parity && global.p1 && global.p2p1; 
    
    action finish0(){
        frame: finish, p2p1;
        pre: !this.finish && !this.parity;
        post: this.finish && global.p2p1;
    }
    
    action finish1(){
        frame: finish, p2p1;
        pre: !this.finish && this.parity;
        post: this.finish && !global.p2p1;
    }
    
    action passBarrier0(){
        frame: parity, finish;
        pre: !this.parity && global.p1 && this.finish;
        post: this.parity && !this.finish;
    }
    
    action passBarrier1(){
        frame: parity, finish;
        pre: this.parity && !global.p1 && this.finish;
        post: !this.parity && !this.finish;
    }
    
    invariant: AG[EF[this.parity]] && AG[EF[!this.parity]];
}


main(){
        p1:proc1;
        p2:proc2;
        run p1();
        run p2();
}

property:  AG[((p1.parity && p2.parity) || (!p1.parity && !p2.parity))];


