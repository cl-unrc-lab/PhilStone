
/*
* This is a version of the arbiter problem
*/

spec arbiter6
send1,send2,send3,send4,send5,send6, r1,r2,r3,r4,r5,r6: prim_boolean;
process process1{
    g1, hasToken: boolean;
    init: !this.g1 && !global.r1; 
    
    action giveGrant(){
        frame: g1;
        pre : !this.g1;
        post: this.g1;
    }
    
    action downGrant(){
        frame: g1;
        pre : global.r1 || !global.r1 ;
        post: !this.g1;
    }
    invariant: AG[EF[global.send2]]&&AG[EF[this.g1]] && AG[EF[!this.g1]];
    }process process2{
    g2, hasToken: boolean;
    init: !this.g2 && !global.r2; 
    
    action giveGrant(){
        frame: g2;
        pre : !this.g2;
        post: this.g2;
    }
    
    action downGrant(){
        frame: g2;
        pre : global.r2 || !global.r2 ;
        post: !this.g2;
    }
    invariant: AG[EF[global.send3]]&&AG[EF[this.g2]] && AG[EF[!this.g2]];
    }process process3{
    g3, hasToken: boolean;
    init: !this.g3 && !global.r3; 
    
    action giveGrant(){
        frame: g3;
        pre : !this.g3;
        post: this.g3;
    }
    
    action downGrant(){
        frame: g3;
        pre : global.r3 || !global.r3 ;
        post: !this.g3;
    }
    invariant: AG[EF[global.send4]]&&AG[EF[this.g3]] && AG[EF[!this.g3]];
    }process process4{
    g4, hasToken: boolean;
    init: !this.g4 && !global.r4; 
    
    action giveGrant(){
        frame: g4;
        pre : !this.g4;
        post: this.g4;
    }
    
    action downGrant(){
        frame: g4;
        pre : global.r4 || !global.r4 ;
        post: !this.g4;
    }
    invariant: AG[EF[global.send5]]&&AG[EF[this.g4]] && AG[EF[!this.g4]];
    }process process5{
    g5, hasToken: boolean;
    init: !this.g5 && !global.r5; 
    
    action giveGrant(){
        frame: g5;
        pre : !this.g5;
        post: this.g5;
    }
    
    action downGrant(){
        frame: g5;
        pre : global.r5 || !global.r5 ;
        post: !this.g5;
    }
    invariant: AG[EF[global.send6]]&&AG[EF[this.g5]] && AG[EF[!this.g5]];
    }process process6{
    g6, hasToken: boolean;
    init: !this.g6 && !global.r6; 
    
    action giveGrant(){
        frame: g6;
        pre : !this.g6;
        post: this.g6;
    }
    
    action downGrant(){
        frame: g6;
        pre : global.r6 || !global.r6 ;
        post: !this.g6;
    }
    invariant: AG[EF[global.send1]]&&AG[EF[this.g6]] && AG[EF[!this.g6]];
    }
main(){
p1:process1;
    p2:process2;
    p3:process3;
    p4:process4;
    p5:process5;
    p6:process6;
    run p1();
    run p2();
    run p3();
    run p4();
    run p5();
    run p6();
    
}
property: G[!global.r1 || F[p1.g1]]&&G[!global.r2 || F[p2.g2]]&&G[!global.r3 || F[p3.g3]]&&G[!global.r4 || F[p4.g4]]&&G[!global.r5 || F[p5.g5]]&&G[!global.r6 || F[p6.g6]]
 &&G[!(p1.g1 && p1.g1)]&&G[!(p1.g1 && p2.g2)]&&G[!(p1.g1 && p3.g3)]&&G[!(p1.g1 && p4.g4)]&&G[!(p1.g1 && p5.g5)]&&G[!(p1.g1 && p6.g6)]&&G[!(p2.g2 && p2.g2)]&&G[!(p2.g2 && p3.g3)]&&G[!(p2.g2 && p4.g4)]&&G[!(p2.g2 && p5.g5)]&&G[!(p2.g2 && p6.g6)]&&G[!(p3.g3 && p3.g3)]&&G[!(p3.g3 && p4.g4)]&&G[!(p3.g3 && p5.g5)]&&G[!(p3.g3 && p6.g6)]&&G[!(p4.g4 && p4.g4)]&&G[!(p4.g4 && p5.g5)]&&G[!(p4.g4 && p6.g6)]&&G[!(p5.g5 && p5.g5)]&&G[!(p5.g5 && p6.g6)]
 &&![(!global.r1 && !p1.g1) U (!global.r1 && p1.g1)]&&![(!global.r2 && !p2.g2) U (!global.r2 && p2.g2)]&&![(!global.r3 && !p3.g3) U (!global.r3 && p3.g3)]&&![(!global.r4 && !p4.g4) U (!global.r4 && p4.g4)]&&![(!global.r5 && !p5.g5) U (!global.r5 && p5.g5)]&&![(!global.r6 && !p6.g6) U (!global.r6 && p6.g6)]
 &&!F[[p1.g1 U [!global.r1 && !p1.g1 U p1.g1 && !global.r1]]]&&!F[[p2.g2 U [!global.r2 && !p2.g2 U p2.g2 && !global.r2]]]&&!F[[p3.g3 U [!global.r3 && !p3.g3 U p3.g3 && !global.r3]]]&&!F[[p4.g4 U [!global.r4 && !p4.g4 U p4.g4 && !global.r4]]]&&!F[[p5.g5 U [!global.r5 && !p5.g5 U p5.g5 && !global.r5]]]&&!F[[p6.g6 U [!global.r6 && !p6.g6 U p6.g6 && !global.r6]]]
 &&G[ !(!global.r1 && p1.g1) || F[(global.r1 && p1.g1) || (!p1.g1)] ]&&G[ !(!global.r2 && p2.g2) || F[(global.r2 && p2.g2) || (!p2.g2)] ]&&G[ !(!global.r3 && p3.g3) || F[(global.r3 && p3.g3) || (!p3.g3)] ]&&G[ !(!global.r4 && p4.g4) || F[(global.r4 && p4.g4) || (!p4.g4)] ]&&G[ !(!global.r5 && p5.g5) || F[(global.r5 && p5.g5) || (!p5.g5)] ]&&G[ !(!global.r6 && p6.g6) || F[(global.r6 && p6.g6) || (!p6.g6)] ];
        assumption: G[F[p1.hasToken]] &&G[F[p2.hasToken]] &&G[F[p3.hasToken]] &&G[F[p4.hasToken]] &&G[F[p5.hasToken]] &&G[F[p6.hasToken]] ;