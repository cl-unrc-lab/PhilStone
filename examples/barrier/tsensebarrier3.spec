/*
Specification for (a tree) sense barrier algorithm described in the book by Fokkink
The leafs are the process and the nodes are the barriers
*/
spec tsensebarrier3

n1, n2n1,  p1n2, p2n2, p3n1: prim_boolean;

process node1{
    parity:boolean;
    owns: n1;
    init: !this.parity &&  !global.n1 && !global.n2n1 && !global.p3n1; 
    
    action passBarrier0(){
        frame: parity, n1;
        pre: !this.parity;/* && global.n2n1 && global.n3n1;*/
        post: this.parity && global.n1;
    }
    
    action passBarrier1(){
        frame: parity, n1;
        pre: this.parity;/* && !global.n2n1 && !global.n3n1;*/
        post: !this.parity && !global.n1;
    }
    
    invariant: AG[EF[this.parity]] && AG[EF[!this.parity]] && AG[!global.n2n1 || EF[global.n1]];
}

process node2{
    parity:boolean;
    owns: n2n1;
    init: !this.parity && !global.p1n2 && !global.p2n2 && !global.n2n1; 
    
    action passBarrier0(){
        frame: parity, n2n1;
        pre: !this.parity;/* && global.p1n2 && global.p2n2;*/
        post: this.parity && global.n2n1;
    }
    
    action passBarrier1(){
        frame: parity, n2n1;
        pre: this.parity;/* && !global.p1n2 && !global.p2n2;*/
        post: !this.parity && !global.n2n1;
    }
    
    invariant: AG[EF[this.parity]] && AG[EF[!this.parity]] &&  AG[!global.p1n2 || !global.p2n2 || EF[global.n2n1]];
}

process proc1{
   parity,finish:boolean;
   owns:p1n2;
    init: !this.finish && !this.parity && !global.n1 && !global.p1n2; 
    
    action finish0(){
        frame: finish, p1n2;
        pre: !this.finish;/* this part whould be guessed: && !this.parity;*/
        post: this.finish && global.p1n2;
    }
    
    action finish1(){
        frame: finish, p1n2;
        pre: !this.finish;/* && this.parity;*/
        post: this.finish && !global.p1n2;
    }
    
    action passBarrier0(){
        frame: parity, finish;
        pre: !this.parity;/* && global.n1 && this.finish;*/
        post: this.parity && !this.finish;
    }
    
    action passBarrier1(){
        frame: parity, finish;
        pre: this.parity; /* && !global.n1 && this.finish;*/
        post: !this.parity && !this.finish;
    }
    
    invariant: AG[EF[this.parity]] && AG[EF[!this.parity]] && AG[EF[global.p1n2]]  && AG[EF[!global.p1n2]];
}

process proc2{
   parity,finish:boolean;
   owns:p2n2;
    init: !this.finish && !this.parity && !global.n1 && !global.p2n2; 
    
    action finish0(){
        frame: finish, p2n2;
        pre: !this.finish && !this.parity;
        post: this.finish && global.p2n2;
    }
    
    action finish1(){
        frame: finish, p2n2;
        pre: !this.finish && this.parity;
        post: this.finish && !global.p2n2;
    }
    
    action passBarrier0(){
        frame: parity, finish;
        pre: !this.parity;/* && global.n1 && this.finish;*/
        post: this.parity && !this.finish;
    }
    
    action passBarrier1(){
        frame: parity, finish;
        pre: this.parity;/* && !global.n1 && this.finish;*/
        post: !this.parity && !this.finish;
    }
    
    invariant: AG[EF[this.parity]] && AG[EF[!this.parity]] && AG[EF[global.p2n2]]  && AG[EF[!global.p2n2]];
}


process proc3{
   parity,finish:boolean;
   owns:p3n1;
    init: !this.finish && !this.parity && !global.n1 && !global.p3n1; 
    
    action finish0(){
        frame: finish, p3n1;
        pre: !this.finish && !this.parity;
        post: this.finish && global.p3n1;
    }
    
    action finish1(){
        frame: finish, p3n1;
        pre: !this.finish && this.parity;
        post: this.finish && !global.p3n1;
    }
    
    action passBarrier0(){
        frame: parity, finish;
        pre: !this.parity;/* && global.n1 && this.finish;*/
        post: this.parity && !this.finish;
    }
    
    action passBarrier1(){
        frame: parity, finish;
        pre: this.parity;/* && !global.n1 && this.finish;*/
        post: !this.parity && !this.finish;
    }
    
    invariant: AG[EF[this.parity]] && AG[EF[!this.parity]] && AG[EF[global.p3n1]]  && AG[EF[!global.p3n1]];
}

main(){
        n1:node1;
        n2:node2;
        p1:proc1;
        p2:proc2;
        p3:proc3;
        run p1();
        run p2();
        run p3();
        run n1();
        run n2();
}

property:  AG[(!p1.finish || !p2.finish || !p3.finish) || (p1.parity && p2.parity && p3.parity) || (!p1.parity && !p2.parity && !p3.parity)];


