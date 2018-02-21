/*********************************************
 * OPL 12.8.0.0 Model
 * Author: David Weiß
 * GitHub: DavidWeissCode
 * Creation Date: Feb 21, 2018
 *********************************************/

/* Questions
- Difference between "range" and array?
*/

// Type definitions
tuple stationType {
  string stationId;
  int employeeCount;
}

// Declarations
range Days = 1..30;
range Employees = 1..10;//TODO: employeeCount should depend on Station[i]
int k = 50;
{int} Stations = ...;
stationType Station[Stations] = ...;//What exactly is happening here? Example farmPlanning

// Decision variables
dvar boolean y[Stations][Employees][Days]; // ToBe night warden shift plan
dvar boolean x[Stations][Employees][Days]; // AsIs night warden shift plan
dvar float o[Stations][Employees][Days];   // Overtime in hours
dvar boolean f[Stations][Employees][Days]; // ToBe shift plan Frühschicht
dvar boolean s[Stations][Employees][Days]; // ToBe shift plan Spätschicht
dvar boolean n[Stations][Employees][Days]; // ToBe shift plan Nachtschicht
dvar boolean u[Stations][Employees][Days]; // Day-off plan
 
// Target function
minimize
  sum(i in Stations, j in 1..Station[i].employeeCount, t in Days)
    (y[i][j][t] - x[i][j][t] + (o[i][j][t]/10));

// Constraints
subject to{

  // (1) ToBe-amount of night warden shifts for house A per month
  sum(i in 1..3, j in 1..10, t in Days)
    y[i][j][t] >= 30;
  
  // (2) ToBe-amount of night warden shifts for house B per month
  sum(i in 4..6, j in 1..10, t in Days)
    y[i][j][t] >= 30;
    
  // (3) ToBe-amount of night warden shifts for house C per month
  sum(i in 7..9, j in 1..10, t in Days)
    y[i][j][t] >= 30;
    
  // (4) ToBe-amount of night warden shifts for house D per month
  sum(i in 10..12, j in 1..10, t in Days)
    y[i][j][t] >= 30;
    
  // (1a) ToBe-amount of night warden shifts is the same for each station in house A
  sum(j in 1..10, t in Days) 
  	x[1][j][t]
  	== sum(j in 1..10, t in Days) 
  		 x[2][j][t] // &&?
  		 == sum(j in 1..10, t in Days) 
  			x[3][j][t];

  // ... (4a)
  
  // (5) Each station has to do at least 3 morning shifts each day
  forall(i in 1..12, t in Days)
    sum(i in 1..12, j in 1..10, t in Days)
      f[i][j][t] >= 3;
      
  // ... (7)
  
  // (8) In house A and C should be at least 1 To-Be night warden per day
  forall(t in Days)
    sum(i in 1..3, j in 1..10)
      x[i][j][t]
      + sum(i in 7..9, j in 1..10)
      	  x[i][j][t] >= 1;
      	  
  // (9) In house B and D should be at least 1 To-Be night warden per day
  forall(t in Days)
    sum(i in 4..6, j in 1..10)
      x[i][j][t]
      + sum(i in 10..12, j in 1..10)
      	  x[i][j][t] >= 1;
      	  
  // (10) An employee can be deployed at max of his available time
  forall(i in 1..12, j in 1..10)
    sum(t in Days)
      (10 * x[i][j][t] + 7.7 * (f[i][j][t] + s[i][j][t]) + 10 * n[i][j][t])
      <= 160 - k - 7.7 * sum(t in Days)
        u[i][j][t]
        + sum(t in Days)
       	  o[i][j][t];
       	  
  // (10a) Day-off upper bound
  forall(i in 1..12)
    sum(j in 1..10, t in Days)
      u[i][j][t] <= (24 * 10) / 12;
      
  // (11) No morning shift after night warden shift
  forall(i in 1..12, j in 1..10, t in Days)
    x[i][j][t] + f[i][j][t] <= 1;
    
  // (12) No morning shift after night shift
  forall(i in 1..12, j in 1..10, t in Days)
    n[i][j][t] + f[i][j][t] <= 1;
    
  // (13) At most one shift per day
  forall(i in 1..12, j in 1..10, t in Days)
    x[i][j][t] + f[i][j][t] + s[i][j][t] + n[i][j][t] <= 1;
    
  // (14) Fairness (siehe 1a)
  
  // (18) Rest at least after 10 days of work
  forall(i in 1..12, j in 1..10, t in Days)
    sum(t in t..t+10)
      x[i][j][t] + f[i][j][t] + s[i][j][t] + n[i][j][t] <= 10;
   
}
