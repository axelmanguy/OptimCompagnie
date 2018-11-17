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
 

// Variables

//Intervals vols
dvar interval VolInterval[v in Vo0] optional in Td[v]..Ta[v] size Dvol[v];
dvar sequence seq[p in Em] in VolInterval;

dvar interval AffectPilot[p in pilots][v in Vo0] optional in Td[v]..Ta[v] size Dvol[v]; //ou in 0..1
dvar interval AffectPN[p in pn][v in Vo0] optional in Td[v]..Ta[v] size Dvol[v];
dvar interval AffectP[p in Em][v in Vo0] optional in Td[v]..Ta[v] size Dvol[v];

dexpr int Npayant[v in Vo0] = Np[v] - sum(p in Em) presenceOf(AffectP[p][v]);

maximize sum(v in Vo0) Npayant[v] ; 
 
constraints {
	forall(p in Em) noOverlap(seq[p]);
	forall(p in pilots) sum(v in Vo0) presenceOf(AffectPilot[p][v]) <= Nvmax;
	forall(p in pn) {
		sum(v in Vo0) presenceOf(AffectPN[p][v]) <= Nvmax;	
	    //sum(v in Vo0)(Dvol[v]*AffectPN[p][v] + ) <=24;		
	}
	forall(p in Em) sum(v in Vo0) presenceOf(AffectP[p][v]) <= Nvmax;
	forall(v in Vo0){
		sum(p in pn) presenceOf(AffectPN[v][p]) == Nec[v];
		sum(p in pilots) presenceOf(AffectPilot[v][p]) == 2;
		//1er aeropot == 
	}
    
}
 

 
