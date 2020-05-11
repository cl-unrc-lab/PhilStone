/* An implementation of the sense barrier algorithm in Fokkink's Book p.169*/
/* p1p2 : p1 notifies p2 that the barrier was reached (global) */
/* p2p1 : p2 notifies p1 that the barrier was reached (global )*/
/* parity: a parity bit two know in which pahes is each process (local)*/
/* finish: a bit indicating if the process has finish the current phase */

spec barrier

p1p2, p2p1: prim_boolean;

process proc1{
    parity, finish:boolean;
    owns: p1p2;  
    init: this.parity && !this.finish && !global.p1p2 &&  !global.p2p1; 
    
    action finish1(){
        frame: finish, parity;
        pre: !this.finish;/*this part should be synthesized*/
        post: this.finish && !this.parity;
    }
    
    action finish0(){
        frame: finish, parity;
        pre: !this.finish && !this.parity;
        post: this.finish && this.parity;
    }
    
    action notifies1(){
        frame: p1p2;
        pre: this.finish && this.parity;
        post: global.p1p2;
    }
    
    action notifies0(){
        frame: p1p2;
        pre: this.finish && !this.parity;
        post: !global.p1p2;
    }
    

    action crossBarrier(){
        frame: finish;
        pre: this.finish; /*should synthesize this condition*/
        post: !this.finish;
    }
   invariant: AG[EF[this.parity]] && AG[EF[!this.parity]];
   
}

process proc2{
    parity,finish:boolean;
    owns: p2p1;  
    init: this.parity && !this.finish && !global.p1p2 &&  !global.p2p1; 
    
    action finish1(){
        frame: finish, parity;
        pre: !this.finish;/*this part should be synthesized*/
        post: this.finish && !this.parity;
    }
    
    action finish0(){
        frame: finish, parity;
        pre: !this.finish && !this.parity;
        post: this.finish && this.parity;
    }
    
    action notifies1(){
        frame: p2p1;
        pre: this.finish && this.parity;
        post: global.p2p1;
    }
    
    action notifies0(){
        frame: p2p1;
        pre: this.finish && !this.parity;
        post: !global.p2p1;
    }
    
    
    action crossBarrier(){
        frame: finish;
        pre: this.finish;
        post: !this.finish;
    }
   invariant: AG[EF[this.parity]] && AG[EF[!this.parity]] && AG[!this.finish || this.parity || A[this.finish U this.parity]] && AG[this.finish || !this.parity || A[this.finish U !this.parity]];
}

main(){
        p1:proc1;
        p2:proc2;
        run p1();
        run p2();
}

property: AG[(p1.finish || p2.finish) || ((p1.parity && p2.parity) || (!p1.parity && !p2.parity))];
