/*Nombre de vols*/
int Nv = ... ;
range Vo = 1..Nv ;
range Vo0 = 0..Nv ;

/*Nombre d'aroports*/
int Na = ... ;
range Ae = 1..Na ;
range Ae0 = 0..Na ;
 
/*Nombre de villes*/
int Ni = ... ;
range Vi = 1..Ni ;
range Vi0 = 0..Ni ;
assert Ni <= Na ;

/*Ville des aroports */
int Va[Ae0] = ... ;
assert forall(a in Ae) 1 <= Va[a] <= Ni ;
 
/*Origine des vols*/
int Ov[Vo0] = ... ;
assert forall(vo in Vo) 1 <= Ov[vo] <= Na ;
/*Destination des vols*/
int Dv[Vo0] = ... ;
assert forall(vo in Vo) 1 <= Dv[vo] <= Na ;

/*Heure de dcollage des vols*/
int Td[Vo0] = ... ;
/*Heure de d'atterrissage des vols*/
int Ta[Vo0] = ... ;
int Dvmin = min(vo in Vo) (Ta[vo]-Td[vo]) ;
assert forall(vo in Vo) 0 <= Td[vo] <= 24 ;
assert forall(vo in Vo) 0 <= Ta[vo] <= 24 ;
assert forall(vo in Vo) Td[vo] <= Ta[vo] ;
 
/*Dure du transit inter-aroport*/
int Dtinf = ... ;
int Dt[Ae0][Ae0] = ... ;
int Dtmin = min(a1,a2 in Ae) Dt[a1][a2] ;
assert forall(ordered a1, a2 in Ae) Dt[a1][a2] == Dt[a2][a1] ;
assert forall(ordered a1, a2 in Ae : Va[a1] != Va[a2]) Dt[a1][a2] == Dtinf ;
 
/*Capacit des vols*/
int Np[Vo0] = ... ;
/*Nombre d'employs en cabine ncessaires sur les vols*/
int Nec[Vo0] = ... ;
assert forall(vo in Vo) Nec[vo] + 2 <= Np[vo] ;
 
/*Prix des places sur les vols*/
int Pr[Vo0] = ... ;
 
/*Nombre d'employs*/
int Ne = ... ;
range Em = 1..Ne ;
 
/*Types possibles (pilote = 1; cabine = 0)*/
range Tys = 0..1 ;
/*Type des employes*/
int Ty[Em] = ... ;
assert forall(e in Em) 0 <= Ty[e] <= 1 ;
/*Ville d'habitation des employs */
int Vh[Em] = ... ;
assert forall(e in Em) 1 <= Vh[e] <= Ni ;
 
/*Nombre d'employs par type et ville d'habitation*/
int Netv[ty in 0..1][vi in Vi] =
    sum(e in Em) ((Ty[e] == ty) && (Vh[e] == vi));

/*Nombre maximum de vols par jour par employ*/
int Nvmax = ... ;
range Ve = 1..Nvmax ;
 
/*Dure maximum d'absence par jour par employ*/
int Dmax = ... ;
 
/*Duree forfaitaire de transfert domicile-aeroport*/
int Dda = ... ;
 
/*Nombre de circuits*/
int Nc = ... ;
range Ci = 1..Nc ;

/*Circuits*/
int Vs[Ci][Ve] = ... ;
/*Nombre de vols dans un circuit*/
int Nvc[ci in Ci] = max(k in Ve) (k * (Vs[ci][k] > 0)) ;
/*Premier et dernier vol d'un circuit*/ 
int Pvc[ci in Ci] = Vs[ci][1] ;
int Dvc[ci in Ci] = Vs[ci][Nvc[ci]] ;
/*Dure d'un circuit*/ 
int Dc[ci in Ci] = (Ta[Dvc[ci]] - Td[Pvc[ci]]) ;
/*Participation d'un vol  un circuit*/
int Vc[vo in Vo][ci in Ci] = (sum(k in Ve) (Vs[ci][k] == vo)) ;
/*Possibilit de participation d'un employe d'une ville  un circuit*/
int Evc[vi in Vi][ci in Ci] = (Va[Ov[Vs[ci][1]]] == vi) ;
 
assert forall(ci in Ci, k in Ve : k <= Nvc[ci]) 1 <= Vs[ci][k] <= Nv ;
assert forall(ci in Ci, ordered k1, k2 in Ve : 
               ((k1 <= Nvc[ci]) && (k2 <= Nvc[ci]))) Vs[ci][k1] != Vs[ci][k2] ;
assert forall(ci in Ci) (Va[Ov[Pvc[ci]]] == Va[Dv[Dvc[ci]]]) ;
assert forall(ci in Ci, k in Ve : (k < Nvc[ci]))
              (Va[Dv[Vs[ci][k]]] == Va[Ov[Vs[ci][k+1]]]) ;
assert forall(ci in Ci, k in Ve : (k < Nvc[ci]))
              (Td[Vs[ci][k+1]] - Ta[Vs[ci][k]] >= Dt[Dv[Vs[ci][k]]][Ov[Vs[ci][k+1]]]) ;
assert forall(ci in Ci) (Dda + Dc[ci]) <= Dmax  ;
              
// Variables

dvar int+ employ[Tys][Ci];

// maximize
/*
	// maximize price
maximize sum (v in Vo) (Pr[v]* (Np[v]+2+Nec[v]-sum(ci in Ci : Vc[v][ci]>0)
(employ[1][ci] + employ[0][ci])));

	// maximize et minimize temps d'absence
maximize sum (v in Vo) (Pr[v]* (Np[v]+2+Nec[v]-sum(ci in Ci : Vc[v][ci]>0)
(employ[1][ci] + employ[0][ci]))) - 0.0001*sum(ci in Ci)(Dc[ci]*(employ[0][ci]+employ[1][ci]));
 */	
 	// maximize et minimize vols
maximize sum (v in Vo) (Pr[v]* (Np[v]+2+Nec[v]-sum(ci in Ci : Vc[v][ci]>0)
(employ[1][ci] + employ[0][ci]))) - 0.0001*sum(ci in Ci)(Nvc[ci]*(employ[0][ci]+employ[1][ci]));
 
 
// constraints {

constraints{


	// constraint - Sur chaque vol, il y a deux pilotes et le personnel correspondant
forall(v in Vo) {
	sum(ci in Ci : Vc[v][ci]>0) employ[1][ci]>=2;
	sum(ci in Ci : Vc[v][ci]>0) employ[0][ci]>=Nec[v];

}		


		
	// constraint - Localisation des employes au depart et l'arrivee du circuit
forall(vi in Vi) {
	forall (t in Tys) {
		sum(ci in Ci : Va[Ov[Pvc[ci]]] == vi) employ[t][ci] <= Netv[t][vi];
	}


}


}
