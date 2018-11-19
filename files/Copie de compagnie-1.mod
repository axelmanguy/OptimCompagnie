using CP;
 
/*Nombre de vols*/
int Nv = ... ;
range Vo = 1..Nv ;
range Vo0 = 0..Nv ;

/*Nombre d'a�roports*/
int Na = ... ;
range Ae = 1..Na ;
range Ae0 = 0..Na ;
 
/*Nombre de villes*/
int Ni = ... ;
range Vi = 1..Ni ;
range Vi0 = 0..Ni ;
assert Ni <= Na ;

/*Ville des a�roports */
int Va[Ae0] = ... ;
assert forall(a in Ae) 1 <= Va[a] <= Ni ;
 
/*Origine des vols*/
int Ov[Vo0] = ... ;
assert forall(v in Vo) 1 <= Ov[v] <= Na ;
/*Destination des vols*/
int Dv[Vo0] = ... ;
assert forall(v in Vo) 1 <= Dv[v] <= Na ;

/*Heure de d�collage des vols*/
int Td[Vo0] = ... ;
/*Heure de d'atterrissage des vols*/
int Ta[Vo0] = ... ;
int Dvmin = min(v in Vo) (Ta[v]-Td[v]) ;
assert forall(v in Vo) 0 <= Td[v] <= 24 ;
assert forall(v in Vo) 0 <= Ta[v] <= 24 ;
assert forall(v in Vo) Td[v] <= Ta[v] ;

int Dvol[v in Vo0] = Ta[v]-Td[v];

 
/*Dur�e du transit inter-a�roport*/
int Dtinf = ... ;
int Dt[Ae0][Ae0] = ... ;
int Dtmin = min(a1,a2 in Ae) Dt[a1][a2] ;
assert forall(ordered a1, a2 in Ae) Dt[a1][a2] == Dt[a2][a1] ;
assert forall(ordered a1, a2 in Ae : Va[a1] != Va[a2]) Dt[a1][a2] == Dtinf ;
 
/*Capacit� des vols*/
int Np[Vo0] = ... ;
/*Nombre d'employ�s en cabine n�cessaires sur les vols*/
int Nec[Vo0] = ... ;
assert forall(v in Vo) Nec[v] + 2 <= Np[v] ;
 
/*Prix des places sur les vols*/
int Pr[Vo0] = ... ;
 
/*Nombre d'employ�s*/
int Ne = ... ;
range Em = 1..Ne ;

/*Type des employ�s (pilote = 1; cabine = 0)*/
int Ty[Em] = ... ;

int NbPilots = sum(e in Em) Ty[e];
range pilots = 1..NbPilots;

int NbPn = sum(e in Em) (1-Ty[e]);
range pn = 1..NbPn;

assert forall(e in Em) 0 <= Ty[e] <= 1 ;
/*Ville d'habitation des employ�s */
int Vh[Em] = ... ;
assert forall(e in Em) 1 <= Vh[e] <= Ni ;

/*Nombre maximum de vols par jour par employ�*/
int Nvmax = ... ;
range Ve = 1..Nvmax ;
range VePlus0 = 0..Nvmax ;

/*Dur�e maximum d'absence par jour par employ�*/
int Dmax = ... ;

/*Duree forfaitaire de transfert domicile-aeroport*/
int Dda = ... ;
 
//Solution à trouver pour micro-compagnie 1
// e1 [0 1 2] pilots
// e2 [0 1 2] pilots
// e3 [0 1 2] cabine
// e4 [0 1 2] cabine
// e5 [0 0 0] cabine
// Variables

//Intervals vols
dvar int SeqPilot[p in pilots][v in Vo0] in Vo0;
dvar int SeqPN[p in pn][v in Vo0] in Vo0;
dvar int SeqP[p in Em][v in Vo0] in Vo0;

/*
dexpr int AffectPilot[p in pilots][v in Vo0] = SeqPilot[p][v] != 0 ; //ou in 0..1
dexpr int AffectPN[p in pn][v in Vo0] = SeqPN[p][v] != 0 ;
dexpr int AffectP[p in Em][v in Vo0] = SeqP[p][v] != 0;*/

dexpr int NbvolPilots[p in pilots] = sum(v in Vo0) SeqPilot[p][v] != 0;
dexpr int NbvolPN[p in pn] = sum(v in Vo0) SeqPN[p][v] != 0;
dexpr int NbvolP[p in Em] = sum(v in Vo0) SeqP[p][v] != 0;

dexpr int Npayant[v in Vo0] = Np[v] - sum(p in Em) (SeqP[p][v] != 0) ;

maximize sum(v in Vo0) Npayant[v] ; 
 
constraints {

	
	SeqPilot[0][0]==0;
	SeqPilot[0][1]==1;
	SeqPilot[0][2]==2;
	SeqPilot[1][0]==0;
	SeqPilot[1][1]==1;
	SeqPilot[1][2]==2;
	
	SeqPN[0][0]==0;
	SeqPN[0][1]==1;
	SeqPN[0][2]==2;
	SeqPN[1][0]==0;
	SeqPN[1][1]==1;
	SeqPN[1][2]==2;
	SeqPN[2][0]==0;
	SeqPN[2][1]==0;
	SeqPN[2][2]==0;
	

	//Contraintes personels pour vols peut-etre un impact
	forall(v in Vo0){
		//2 pilots par vol
		(sum(p in pilots) (SeqPilot[p][v] != 0)) >=2;
		//Nec personel naviguant par vol
		(sum(p in pn) (SeqPN[p][v] != 0)) >= Nec[v];
	}
	
	//Contraintes sur les personels
	forall(p in pilots){
		//nombre de vol maximum
		NbvolPilots[p] <= Nvmax;
		//ville de depart = ville d'origine
		
		NbvolPilots[p]>0 => Va[Ov[SeqPilot[p][1]]] == Vh[p];
		//ville d'arrivée= ville d'origine'
		NbvolPilots[p]>0 =>Va[Dv[SeqPilot[p][NbvolPilots[p]]]] == Vh[p];
		//derniere date + trajet <= 24
		NbvolPilots[p]>0 =>Ta[SeqPilot[p][NbvolPilots[p]]] + Dda <=24;
		//Decollage == 0
		NbvolPilots[p]>0 =>Td[SeqPilot[p][1]] >= 0;
	}
	forall(p in pn){
		NbvolPN[p] <= Nvmax;
		
		NbvolPN[p]>0 =>Va[Ov[SeqPN[p][1]]] == Vh[p];
		//ville d'arrivée= ville d'origine'
		NbvolPN[p]>0 =>Va[Dv[SeqPN[p][NbvolPN[p]]]] == Vh[p];
		//derniere date + trajet <= 24
		NbvolPN[p]>0 =>Ta[SeqPN[p][NbvolPN[p]]] +Dda <=24;
		//Decollage == 0
		NbvolPN[p]>0 =>Td[SeqPN[p][1]] >= 0;
	}
	
	forall(p in pilots,v in Ve : v < Nvmax){
		//temps de transit	
		v < NbvolPilots[p] => Td[v+1]-Ta[v] >= Dt[Ov[v+1]][Dv[v]];
		//sequence
		v < NbvolPilots[p] => Td[v+1] >= Ta[v];
		
	}
	forall(p in pn,v in Ve : v < Nvmax){
		v < NbvolPN[p] => Td[v+1]-Ta[v] >= Dt[Ov[v+1]][Dv[v]];
		v < NbvolPN[p] => Td[v+1] >= Ta[v];
	}
    
}
 

 
