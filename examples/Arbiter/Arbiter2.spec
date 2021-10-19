spec arbiter
send1, send2, r1, r2:prim_boolean;

process process1{
    g1, hasToken: boolean;
    init: !this.g1 && !global.r1; 
    
    
    action giveGrant(){
        frame: g1;
        pre :!this.g1 || this.g1 ;
        post: this.g1;
    }
    
    action downGrant(){
        frame: g1;
        pre : !this.g1 || this.g1;
        post: !this.g1;
    }
    
    
    invariant: AG[!this.hasToken || EF[global.send2]] && AG[EF[this.g1]] && AG[EF[!this.g1]] ;
}

process process2{
    g2, hasToken  : boolean;
    init: !this.g2 && !global.r2; 
    
    
    action giveGrant(){
        frame: g2;
        pre : !this.g2 || this.g2 ;
        post: this.g2;
    }
    
    action downGrant(){
        frame: g2;
        pre : !this.g2 || this.g2;
        post: !this.g2;
    }
    
    
    invariant:  AG[!this.hasToken || EF[global.send1]] ;
}


main(){
    p1:process1;
    p2:process2;
    run p1();
    run p2();
} 

/* Temporal Spec */

property: 
              G[!global.r1 || F[p1.g1]]
          &&  G[!global.r2 || F[p2.g2]] 
          &&  G[!(p1.g1 && p2.g2)];
       

assumption: G[!global.r1 || p1.g1 || [global.r1 W  p1.g1]]
            && G[global.r1 || !p1.g1 || [!global.r1 W  !p1.g1]]
            && G[!global.r2 || p2.g2 || [global.r2 W  p2.g2]] 
            && G[global.r2 || !p2.g2 || [!global.r2 W  !p2.g2]]
            && G[F[!p1.g1 || !global.r1]] 
            && G[F[!p2.g2 || !global.r2]];

