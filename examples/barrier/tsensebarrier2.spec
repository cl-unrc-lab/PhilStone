/*
Specification for the tournament sense barrier algorithm described in the book "Distributed Algorithms: An Intuitive Approach" by Fokkink
The leafs are the process and the nodes are the barriers.
*/
spec tsensebarrier2

n1,  p1n1, p2n1 : prim_boolean;

/*
* This is the  barrier when all the processes passed the barrier it announces the result
*/
process node1{
    parity:boolean;
    owns: n1;
    init: !this.parity &&  !global.n1 && !global.p1n1 && !global.p2n1; 
    
    action passBarrier0(){
        frame: parity, n1;
        pre: !this.parity;/* This part should be guessed by the synthesizer && global.n2n1 && global.n3n1;*/
        post: this.parity && global.n1;
    }
    
    action passBarrier1(){
        frame: parity, n1;
        pre: this.parity;/* && !global.n2n1 && !global.n3n1;*/
        post: !this.parity && !global.n1;
    }
    
    invariant: AG[EF[this.parity]] && AG[EF[!this.parity]];
}

/*
* A simple definition of a process, each process has a local parity, this together with the global parity
* allows one to know whether the process has to pass the barrier or not
*/ 
process proc1{
   parity,finish:boolean;
   owns:p1n1;
   init: !this.finish && !this.parity && !global.n1 && !global.p1n1; 
    
    /* This is used to indicate that it has arrived to the barrier 0
    *  finish means that the process has arrived to the barrier
    */
    action finish0(){
        frame: finish, p1n1;
        pre: !this.finish;/* this part whould be guessed: && !this.parity;*/
        post: this.finish && global.p1n1;
    }
    /* This is used to indicate that it has arrived to the barrier 1 */
    action finish1(){
        frame: finish, p1n1;
        pre: !this.finish;/* && this.parity;*/
        post: this.finish && !global.p1n1;
    }
    
    /* The parity is changed when the barrier gives the signal */
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
    
    invariant: AG[EF[this.parity]] && AG[EF[!this.parity]] && AG[EF[global.p1n1]]  && AG[EF[!global.p1n1]];
}
/* This is similar to process 1 */
process proc2{
   parity,finish:boolean;
   owns:p2n1;
    init: !this.finish && !this.parity && !global.n1 && !global.p2n1; 
    
    action finish0(){
        frame: finish, p2n1;
        pre: !this.finish && !this.parity;
        post: this.finish && global.p2n1;
    }
    
    action finish1(){
        frame: finish, p2n1;
        pre: !this.finish && this.parity;
        post: this.finish && !global.p2n1;
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
    
    invariant: AG[EF[this.parity]] && AG[EF[!this.parity]] && AG[EF[global.p2n1]]  && AG[EF[!global.p2n1]];
}

main(){
        n1:node1;
        p1:proc1;
        p2:proc2;
        run p1();
        run p2();
        run n1();
}

/* Safety property: If the processes have finished then the parities coincide */
property:  AG[(!p1.finish || !p2.finish) || (p1.parity && p2.parity) || (!p1.parity && !p2.parity)];


