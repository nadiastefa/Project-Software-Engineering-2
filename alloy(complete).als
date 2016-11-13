open util/boolean

//----DATA-----//

sig System{
	cars: some Car,
	registeredUser: some User,
	reservation: some Reservation,
	safeArea: some SafeArea,
	ride: some Ride
}
{
	cars.status = Available
}

sig Car {
	id: Int,
	status: one CarStatus,
	position: one Coordinates,
	battery: Int
}
{
	battery >=0 and battery<=7
}

sig Coordinates{
	latitude: Int,
	longitude: Int
}

sig Email, Password{}

sig User {
	registration : one Registration,
	password: one Password,
}

sig Date, Time,License,CreditCard{}

sig Registration {
	birthday: one Date,
	email: one Email,
	license: one License,
	paymentInformation: one CreditCard
}

sig SafeArea{
	availableCars: set Car,
	position: one Coordinates
}

sig PowerGrid{
	available : one Bool
}

sig SpecialSafeArea extends SafeArea{
	capacity: set PowerGrid,
	chargingCars: set Car
}
{
 	#capacity>0 and #chargingCars<=#capacity
} 

sig Reservation {
	car : one Car,
	user:  one User
}
{
	car.status=Reserved
}

sig Fare {
	price: one Int,
	payment: one CreditCard
}
{ 
	price>=0
}

sig Ride {
	reservation: one Reservation,
	fare: one Fare,
	position: one Coordinates
}


//----ABSTRACT-DATA-----//

abstract sig CarStatus{}

sig Available extends CarStatus{}

sig Reserved extends CarStatus{}

sig InUse extends CarStatus{}

sig OutOfService extends CarStatus{}


//-----FACTS----//

fact lowBatteryCarInSafe{
	all c:System.cars | all s:SpecialSafeArea| (c.battery<4 and c.status=Available) implies  c.position=s.position
}

fact IDCarsAreUnique {
	all c1,c2: Car | (c1 != c2) => c1.id != c2.id
}

fact  noDupEmail{
	no disj u1,u2: User | u1 != u2 and u1.registration.email = u2.registration.email
}

fact noSameRegistration{
	all r1,r2: Registration | r1!=r2 implies (r1.email!=r2.email and r1.license!=r2.license) 
}

fact noUserOutOfSystem {
	all u:User | 	some s: System | u in s.registeredUser
}

fact availableCarsAreInSafe{
	all c: System.cars | all s:SafeArea | c.status = Available implies c.position=s.position
}

fact positionIsConsistance{
	all c: Car | all s: SafeArea | c in s.availableCars implies c.position = s.position 
}


fact areaPositionAreUnique{
	all a1,a2: SafeArea | (a1 != a2) => a1.position != a2.position
}

fact noSameReservation{
	all r1,r2: Reservation | r1!=r2 implies (r1.car!=r2.car and r1.user!=r2.user) 
}

fact reservationToOneRide {
	all r1,r2: Ride | r1!=r2 implies r1.reservation!=r2.reservation
}

fact userReservedCarAlreadyUse {
	all r: Ride | r.reservation.user.registration.paymentInformation=r.fare.payment
}

fact carPositionMove {
	all r: Ride | r.reservation.car.position= r.position
}


//----ASSERTS----//

assert noDoubleCarsInReservation{
	no disj c1,c2:Car, r:Reservation | r.car=c1 and r.car=c2 and c1=c2
}
check noDoubleCarsInReservation for 3

assert noDoubleUserInReservation{
	no disj u1,u2:User, r:Reservation | r.user=u1 and r.user=u2 and u1=u2
}
check noDoubleUserInReservation for 3


//---PREDICATES----//

pred show() {
	#System=1
	#Reservation>0
	#Ride>0
}
run show for 3

pred addRegistration (r: Registration, s1,s2: System){
	r not in s1.registeredUser.registration implies s2. registeredUser.registration=s1. registeredUser.registration+r
}
run addRegistration for 3

pred addReservation (r: Reservation, s1,s2: System){
 	r not in s1.reservation implies s2.reservation=s1.reservation+r and r.car.status=Reserved
}
run addReservation  for 3

pred deleteReservation(r: Reservation, s1,s2: System){
 	r in s1.reservation implies s2.reservation=s1.reservation-r and r.car.status=Available
}
run deleteReservation for 4

pred addRide(r: Ride, s1,s2: System){
	(r not in s1.ride and r.reservation in s1.reservation) implies s2. ride=s1. ride+r
}
run addRide for 3

pred deleteRide(r:Ride, s1,s2: System){
	r in s1.ride implies s2.ride=s1.ride-r and s2.reservation=s1.reservation-r.reservation and r.reservation.car.status=Available
}
run deleteRide for 4

 

