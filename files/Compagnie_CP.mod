using CP;
 
/*Nombre de vols*/
int Nv = ... ;
range Vo = 1..Nv ;
range Vo0 = 0..Nv ;

/*Nombre d'aeroports*/
int Na = ... ;
range Ae = 1..Na ;
range Ae0 = 0..Na ;
 
/*Nombre de villes*/
int Ni = ... ;
range Vi = 1..Ni ;
range Vi0 = 0..Ni ;
assert Ni <= Na ;

/*Ville des aeroports */
int Va[Ae0] = ... ;
assert forall(a in Ae) 1 <= Va[a] <= Ni ;
 
/*Origine des vols*/
int Ov[Vo0] = ... ;
assert forall(v in Vo) 1 <= Ov[v] <= Na ;
/*Destination des vols*/
int Dv[Vo0] = ... ;
assert forall(v in Vo) 1 <= Dv[v] <= Na ;

/*Heure de decollage des vols*/
int Td[Vo0] = ... ;
/*Heure de d'atterrissage des vols*/
int Ta[Vo0] = ... ;
int Dvmin = min(v in Vo) (Ta[v]-Td[v]) ;
assert forall(v in Vo) 0 <= Td[v] <= 24 ;
assert forall(v in Vo) 0 <= Ta[v] <= 24 ;
assert forall(v in Vo) Td[v] <= Ta[v] ;

 
/*Duree du transit inter-aeroport*/
int Dtinf = ... ;
int Dt[Ae0][Ae0] = ... ;
int Dtmin = min(a1,a2 in Ae) Dt[a1][a2] ;
assert forall(ordered a1, a2 in Ae) Dt[a1][a2] == Dt[a2][a1] ;
assert forall(ordered a1, a2 in Ae : Va[a1] != Va[a2]) Dt[a1][a2] == Dtinf ;
 
/*Capacite des vols*/
int Np[Vo0] = ... ;
/*Nombre d'employes en cabine necessaires sur les vols*/
int Nec[Vo0] = ... ;
assert forall(v in Vo) Nec[v] + 2 <= Np[v] ;
 
/*Prix des places sur les vols*/
int Pr[Vo0] = ... ;
 
/*Nombre d'employes*/
int Ne = ... ;
range Em = 1..Ne ;

/*Type des employes (pilote = 1; cabine = 0)*/
int Ty[Em] = ... ;
assert forall(e in Em) 0 <= Ty[e] <= 1 ;
/*Ville d'habitation des employes */
int Vh[Em] = ... ;
assert forall(e in Em) 1 <= Vh[e] <= Ni ;

/*Nombre maximum de vols par jour par employe*/
int Nvmax = ... ;
range Ve = 1..Nvmax ;
range VePlus0 = 0..Nvmax ;

/*Duree maximum d'absence par jour par employe*/
int Dmax = ... ;

/*Duree forfaitaire de transfert domicile-aeroport*/
int Dda = ... ;
 

// Variable de decision
dvar int affectation[e in Em][v in VePlus0] in Vo0;

// expression de calcul
//nombre de vol par employees
dexpr int NbVolEmp[e in Em] = sum(v in Ve)(affectation[e][v] !=0);

//nombre de pilotes par vol
dexpr int NbPilotVol[v in Vo] = sum(e in Em, v2 in Ve)(affectation[e][v2] ==v && Ty[e] ==0);
//nombre de PersonelCabine par vol
dexpr int NbPcVol[v in Vo] = sum(e in Em, v2 in Ve)(affectation[e][v2] ==v && Ty[e] ==1);

//benefices des vols (tout les emplyee -2 pilotes - le nombre de personel)
dexpr int ben = sum(v in Vo) (Np[v]-(NbPilotVol[v]+2)-(NbPcVol[v]+Nec[v]))*Pr[v];

maximize ben; 
 
constraints {

//Contraintes sur les personels de bords
forall(v in Vo){
	NbPilotVol[v] >= 2;
	NbPcVol[v] >= Nec[v];
}
//Contraintes sur les employees
forall(e in Em){
	NbVolEmp[e] > 0 => Va[Ov[affectation[e][1]]]==Vh[e];
	NbVolEmp[e] > 0 => Va[Dv[affectation[e][NbVolEmp[e]]]] == Vh[e];
	Ta[affectation[e][NbVolEmp[e]]]-Td[affectation[e][1]]+Dda <= Dmax;
}

//Contraintes logiques sur les vols
forall(e in Em){
	forall(v in 1..(Nvmax-1)){
	affectation[e][v] >0 && affectation[e][v+1] >0 => 
	Td[affectation[e][v+1]] - Ta[affectation[e][v]] >=
	Dt[Dv[affectation[e][v]]][Ov[affectation[e][v+1]]];
	}
}
//Contrainte de succesion des vols
forall(e in Em){
	forall(v,v2 in Ve : v < v2){
		v2<	NbVolEmp[e] => Td[affectation[e][v]] < Td[affectation[e][v]];
	}
}
//Contrainte de fin du tableau
forall(e in Em){
	forall(v in Ve){
	v <	NbVolEmp[e] => affectation[e][v] >0;
	}
}
//Contrainte d'intialisation
forall(e in Em){
	affectation[e][0]==0;
	}
//Contrainte de difference des vols realisés
forall(e in Em){
	forall(v,v2 in Ve : v<v2){
	v2 < NbVolEmp[e] => affectation[e][v] != affectation[e][v2];
	}
}
}
