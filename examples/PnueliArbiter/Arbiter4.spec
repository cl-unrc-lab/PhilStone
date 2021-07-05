/* Pnueli Arbiter for 3 processes */
spec arbiter
send1, send2, send3, send4, r1, r2, r3, r4:prim_boolean;

process process1{
    g1, hasToken: boolean;
    init: !this.g1 && !global.r1; 
    
    
    action giveGrant(){
        frame: g1;
        pre :!this.g1 ;
        post: this.g1;
    }
    
    action downGrant(){
        frame: g1;
        pre : this.g1;
        post: !this.g1;
    }
    
    
    invariant: AG[!this.hasToken || EF[global.send2]] && AG[EF[this.g1]] && AG[EF[!this.g1]] ;
}

process process2{
    g2, hasToken  : boolean;
    init: !this.g2 && !global.r2; 
    
    
    action giveGrant(){
        frame: g2;
        pre : !this.g2  ;
        post: this.g2;
    }
    
    action downGrant(){
        frame: g2;
        pre : this.g2 ;
        post: !this.g2;
    }
    
    
    invariant:  AG[!this.hasToken || EF[global.send3]] ;
}

process process3{
    g3, hasToken  : boolean;
    init: !this.g3 && !global.r3; 
    
    
    action giveGrant(){
        frame: g3;
        pre : !this.g3  ;
        post: this.g3;
    }
    
    action downGrant(){
        frame: g3;
        pre : this.g3 ;
        post: !this.g3;
    }
    
    
    invariant:  AG[!this.hasToken || EF[global.send4]] ;
}

process process4{
    g4, hasToken  : boolean;
    init: !this.g4 && !global.r4; 
    
    
    action giveGrant(){
        frame: g4;
        pre : !this.g4  ;
        post: this.g4;
    }
    
    action downGrant(){
        frame: g4;
        pre : this.g4 ;
        post: !this.g4;
    }
    
    
    invariant:  AG[!this.hasToken || EF[global.send1]] ;
}



main(){
    p1:process1;
    p2:process2;
    p3:process3;
    p4:process4;
    run p1();
    run p2();
    run p3();
    run p4();
} 

/* Temporal Spec */

property:  
             G[!global.r1 || !p1.g1 || [p1.g1 W !global.r1]] /* Grant keeps high until request is down */
          && G[global.r1 || p1.g1 || [!p1.g1 W global.r1]]   /* Grant keeps low until request is up */
          && G[!global.r2 || !p2.g2 || [p2.g2 W !global.r2]] /* Grant keeps high until request is down */
          && G[global.r2 || p2.g2 || [!p2.g2 W global.r2 ]]  /* Grant keeps low until request is up */
          && G[!global.r3 || !p3.g3 || [p3.g3 W !global.r3]] /* Grant keeps high until request is down */
          && G[global.r3 || p3.g3 || [!p3.g3 W global.r3 ]]  /* Grant keeps low until request is up */
           && G[!global.r4 || !p4.g4 || [p4.g4 W !global.r4]] /* Grant keeps high until request is down */
          && G[global.r4 || p4.g4 || [!p4.g4 W global.r4 ]]  /* Grant keeps low until request is up */
          && G[F[(global.r1 && p1.g1) || (!global.r1 && !p1.g1)]] /* eventually grants and requests coincide */
          && G[F[(global.r2 && p2.g2) || (!global.r2 && !p2.g2)]]
          && G[F[(global.r3 && p3.g3) || (!global.r3 && !p3.g3)]]
           && G[F[(global.r4 && p4.g4) || (!global.r4 && !p4.g4)]]
          && G[!(p1.g1 && p2.g2) && !(p1.g1 && p3.g3) && !(p2.g2 && p3.g3) 
                && !(p1.g1 && p4.g4) && !(p2.g2 && p4.g4) && !(p3.g3 && p4.g4) ]; /* mutual exclusion */
       

assumption:    G[!global.r1 || p1.g1 || [global.r1 W  p1.g1]]   /*Requests keeps hight until a grant is given*/
            && G[global.r1 || !p1.g1 || [!global.r1 W  !p1.g1]] /*If a grant was given, the request keeps down until the grant is down*/
            && G[!global.r2 || p2.g2 || [global.r2 W  p2.g2]]   /*Requests keeps hight until a grant is given*/
            && G[global.r2 || !p2.g2 || [!global.r2 W  !p2.g2]] /*If a grant was given, the request keeps down until the grant is down*/
            && G[!global.r3 || p3.g3 || [global.r3 W  p3.g3]]   /*Requests keeps hight until a grant is given*/
            && G[global.r3 || !p3.g3 || [!global.r3 W  !p3.g3]] /*If a grant was given, the request keeps down until the grant is down*/
            && G[!global.r4 || p4.g4 || [global.r4 W  p4.g4]]   /*Requests keeps hight until a grant is given*/
            && G[global.r4 || !p4.g4 || [!global.r4 W  !p4.g4]] /*If a grant was given, the request keeps down until the grant is down*/ 
            && G[F[!p1.g1 || !global.r1]] /* eventually grants or requests get down*/         
            && G[F[!p2.g2 || !global.r2]]
            && G[F[!p3.g3 || !global.r3]]
            && G[F[!p4.g4 || !global.r4]];


            