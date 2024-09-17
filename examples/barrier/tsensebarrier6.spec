/*
* Specification for  sense barrier algorithm described in the book by Fokkink
* The leafs are the process and the nodes are the barriers
*/
spec tsensebarrier5

n1, n2n4, n3n4, p1n2, p2n2, p3n3, p4n3, p5n5, n5n1, n4n1, p6n5: prim_boolean;

process node1{
    parity:boolean;
    owns: n1;
    init: !this.parity &&  !global.n1 && !global.n4n1 && !global.n5n1; 
    
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
    
    invariant: AG[EF[this.parity]] && AG[EF[!this.parity]] && AG[!global.n4n1 || !global.n5n1 || EF[global.n1]];
}

process node2{
    parity:boolean;
    owns: n2n4;
    init: !this.parity && !global.p1n2 && !global.p2n2 && !global.n2n4; 
    
    action passBarrier0(){
        frame: parity, n2n4;
        pre: !this.parity;/* && global.p1n2 && global.p2n2;*/
        post: this.parity && global.n2n4;
    }
    
    action passBarrier1(){
        frame: parity, n2n4;
        pre: this.parity;/* && !global.p1n2 && !global.p2n2;*/
        post: !this.parity && !global.n2n4;
    }
    
    invariant: AG[EF[this.parity]] && AG[EF[!this.parity]] &&  AG[!global.p1n2 || !global.p2n2 || EF[global.n2n4]];
}

process node3{
    parity:boolean;
    owns: n3n4;
    init: !this.parity &&  !global.n2n4 && !global.p3n3 && !global.p4n3; 
    
    action passBarrier0(){
        frame: parity, n2n4;
        pre: !this.parity;/* && global.p3n3 && global.p4n3;*/
        post: this.parity && global.n2n4;
    }
    
    action passBarrier1(){
        frame: parity, n2n4;
        pre: this.parity;/* && !global.p3n3 && !global.p4n3;*/
        post: !this.parity && !global.n2n4;
    }
    
    invariant: AG[EF[this.parity]] && AG[EF[!this.parity]] && AG[!global.p3n3 || !global.p4n3 || EF[global.n3n4]];
}

process node4{
    parity:boolean;
    owns: n4n1;
    init: !this.parity &&  !global.n2n4 && !global.n3n4 && !global.n4n1; 
    
    action passBarrier0(){
        frame: parity, n4n1;
        pre: !this.parity;
        post: this.parity && global.n4n1;
    }
    
    action passBarrier1(){
        frame: parity, n4n1;
        pre: this.parity;
        post: !this.parity && !global.n4n1;
    }
    
    invariant: AG[EF[this.parity]] && AG[EF[!this.parity]] && AG[!global.n3n4 || EF[global.n4n1]];
}


process node5{
    parity:boolean;
    owns: n5n1;
    init: !this.parity &&   !global.p5n5 && !global.p6n5 && !global.n5n1; 
    
    action passBarrier0(){
        frame: parity, n5n1;
        pre: !this.parity;
        post: this.parity && global.n5n1;
    }
    
    action passBarrier1(){
        frame: parity, n5n1;
        pre: this.parity;
        post: !this.parity && !global.n5n1;
    }
    
    invariant: AG[EF[this.parity]] && AG[EF[!this.parity]] && AG[!global.p5n5 || EF[global.n5n1]];
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
   owns:p3n3;
    init: !this.finish && !this.parity && !global.n1 && !global.p3n3; 
    
    action finish0(){
        frame: finish, p3n3;
        pre: !this.finish && !this.parity;
        post: this.finish && global.p3n3;
    }
    
    action finish1(){
        frame: finish, p3n3;
        pre: !this.finish && this.parity;
        post: this.finish && !global.p3n3;
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
    
    invariant: AG[EF[this.parity]] && AG[EF[!this.parity]] && AG[EF[global.p3n3]]  && AG[EF[!global.p3n3]];
}

process proc4{
   parity,finish:boolean;
   owns:p4n3;
    init: !this.finish && !this.parity && !global.n1 && !global.p4n3; 
    
    action finish0(){
        frame: finish, p4n3;
        pre: !this.finish;/* && !this.parity;*/
        post: this.finish && global.p4n3;
    }
    
    action finish1(){
        frame: finish, p4n3;
        pre: !this.finish;/* && this.parity;*/
        post: this.finish && !global.p4n3;
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
    
    invariant: AG[EF[this.parity]] && AG[EF[!this.parity]] && AG[EF[global.p4n3]]  && AG[EF[!global.p4n3]];
}

process proc5{
    parity,finish:boolean;
    owns:p5n5;
     init: !this.finish && !this.parity && !global.n1 && !global.p5n5; 
     
     action finish0(){
         frame: finish, p5n5;
         pre: !this.finish;/* && !this.parity;*/
         post: this.finish && global.p5n5;
     }
     
     action finish1(){
         frame: finish, p5n5;
         pre: !this.finish;/* && this.parity;*/
         post: this.finish && !global.p5n5;
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
     
     invariant: AG[EF[this.parity]] && AG[EF[!this.parity]] && AG[EF[global.p5n5]]  && AG[EF[!global.p5n5]];
 }
 process proc6{
    parity,finish:boolean;
    owns:p6n5;
     init: !this.finish && !this.parity && !global.n1 && !global.p6n5; 
     
     action finish0(){
         frame: finish, p6n5;
         pre: !this.finish;/* && !this.parity;*/
         post: this.finish && global.p6n5;
     }
     
     action finish1(){
         frame: finish, p6n5;
         pre: !this.finish;/* && this.parity;*/
         post: this.finish && !global.p6n5;
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
     
     invariant: AG[EF[this.parity]] && AG[EF[!this.parity]] && AG[EF[global.p6n5]]  && AG[EF[!global.p6n5]];
 }




main(){
        n1:node1;
        n2:node2;
        n3:node3;
        n4:node4;
        n5:node5;
        p1:proc1;
        p2:proc2;
        p3:proc3;
        p4:proc4;
        p5:proc5;
        p6:proc6;
        run n1();
        run n2();
        run n3();
        run n4();
        run n5();
        run p1();
        run p2();
        run p3();
        run p4();
        run p5();
        run p6();


}

property:  AG[(!p1.finish || !p2.finish || !p3.finish || !p4.finish || !p5.finish || !p6.finish) || (p1.parity && p2.parity && p3.parity  &&  p4.parity && p5.parity && p6.parity) || (!p1.parity && !p2.parity && !p3.parity && !p4.parity && !p5.parity && !p6.parity)];
