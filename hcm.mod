/*********************************************
 * OPL 12.8.0.0 Model
 * Author: David Weiß
 * GitHub: DavidWeissCode
 * Creation Date: Feb 21, 2018
 *********************************************/

/* Notes
- cplex ranges are of type int
- decision variables depend on ranges
- restrict calculation with ops file
*/

// Declarations
int stationAmount = 11;
int employeeAmount = 13;
float k = 0.05;  // Sickness rate (in 0..1)
float w_o = 0.5; // Weight for overtime penalty (in 0..infinity)
float w_f = 0.5; // Weight for fairness penalty (in 0..infinity)
int fMax = 5;    // Maximal amount of shifts before shift change
int sMax = 5;
int nMax = 5;
int xMax = 5;

range Station = 1..stationAmount;
range Employee = 1..employeeAmount;
range Day = 1..30;

//int u[Station][Employee][Day] = ...; 	// Day-off plan // Cannot read/write 3-dim data from .xls

// Decision variables
dvar int x[Station][Employee][Day] in 0..1; // ToBe night warden shift plan ("Soll")
dvar int f[Station][Employee][Day] in 0..1; // ToBe shift plan Frühschicht
dvar int s[Station][Employee][Day] in 0..1;	// ToBe shift plan Spätschicht
dvar int n[Station][Employee][Day] in 0..1;	// ToBe shift plan Nachtschicht
dvar int o[Station][Employee][Day] in 0..1;	// Overtime in hours

// Target function
minimize
  120 - sum(i in Station, j in Employee, t in Day) ( // One night warden per house per day --> 4 houses * 30 days == 120
  	(x[i][j][t] - w_o * (o[i][j][t]))                // Penalize overtime of individuals
  ) + w_f * (                                        // Penalize night warden shift unfairness between stations
    sum(i in 1..9) (								 // Fairness between stations 1-9
      abs(
        sum(j in Employee, t in Day) (
          x[i][j][t]
        ) - (
          sum(i in 1..9, j in Employee, t in Day) (
            x[i][j][t]
          )
        ) / 9
      )
    ) + sum(i in 10..11) (						     // Fairness between stations 10-11
      abs(
        sum(j in Employee, t in Day) (
          x[i][j][t]
        ) - (
          sum(i in 10..11, j in Employee, t in Day) (
            x[i][j][t]
          )
        ) / 2
      )
    ));

// Constraints
subject to{

  // (1) Each station has to do at least 3 morning shifts each day
  forall(i in Station, t in Day)
    sum(j in Employee)
      f[i][j][t] >= 3;
      
  // (2) Each station has to do at least 2 evening shifts each day
  forall(i in Station, t in Day)
    sum(j in Employee)
      s[i][j][t] >= 2;
      
  // (3) Each station has to do at least 1 night shifts each day
  forall(i in Station, t in Day)
    sum(j in Employee)
      n[i][j][t] >= 1;
    	  
  // (4) In house H1 and H3 should be at least 1 ToBe night warden per day
  forall(t in Day) (
  	sum(i in 1..3, j in Employee) (
	  x[i][j][t]
    ) +
    sum(i in 7..9, j in Employee) (
      x[i][j][t]
    ) >= 1
  );
  
  // (5) In house H2 and H4 should be at least 1 ToBe night warden per day
  forall(t in Day) (
  	sum(i in 4..6, j in Employee) (
	  x[i][j][t]
    ) +
    sum(i in 10..11, j in Employee) (
      x[i][j][t]
    ) >= 1
  );

  // (6) An employee can be deployed at max of his available time per month
  forall(i in Station, j in Employee) (
  	sum(t in Day) (
  	  (10 * x[i][j][t] + 7.7 * (f[i][j][t] + s[i][j][t]) + 10 * n[i][j][t])
  	) <= (160 - k * 160 - 16.17 + sum(t in Day) (
  	  o[i][j][t] * 10
  	))
  );

  // (7) No morning shift after night warden shift
  forall(i in Station, j in Employee, t in 1..29)
    x[i][j][t] + f[i][j][t+1] <= 1;
    
  // (8) No morning shift after night shift
  forall(i in Station, j in Employee, t in 1..29)
    n[i][j][t] + f[i][j][t+1] <= 1;
    
  // (7a) No evening shift after night warden shift
  forall(i in Station, j in Employee, t in 1..29)
    x[i][j][t] + s[i][j][t+1] <= 1;
    
  // (8a) No evening shift after night shift
  forall(i in Station, j in Employee, t in 1..29)
    n[i][j][t] + s[i][j][t+1] <= 1;
    
  // (9) At most one shift per day
  forall(i in Station, j in Employee, t in Day)
    x[i][j][t] + f[i][j][t] + s[i][j][t] + n[i][j][t] + o[i][j][t] <= 1;
  
  // (10) Rest at least after 10 days of work
  forall(i in Station, j in Employee, t in Day) (
    sum(th in t..t+10: t <= 20)
      (x[i][j][th] + f[i][j][th] + s[i][j][th] + n[i][j][th] + o[i][j][th]) <= 10
  );
    
  // (11) Rotation of morning shifts
  forall(i in Station, j in Employee)
    sum(t in Day)
      f[i][j][t] <= fMax;
      
  // (12) Rotation of evening shifts
  forall(i in Station, j in Employee)
    sum(t in Day)
      s[i][j][t] <= sMax;
      
  // (13) Rotation of night shifts
  forall(i in Station, j in Employee)
    sum(t in Day)
      n[i][j][t] <= nMax;
      
  // (14) Rotation of house warden shifts
  forall(i in Station, j in Employee)
    sum(t in Day)
      x[i][j][t] <= xMax;
      
  // (15) Maximum night warden shifts per day in house H1
  forall(t in Day)
    sum(i in 1..3, j in Employee)
      x[i][j][t] <= 1;
      
  // (16) Maximum night warden shifts per day in house H2
  forall(t in Day)
    sum(i in 4..6, j in Employee)
      x[i][j][t] <= 1;
      
  // (17) Maximum night warden shifts per day in house H3
  forall(t in Day)
    sum(i in 7..9, j in Employee)
      x[i][j][t] <= 1;
      
  // (18) Maximum night warden shifts per day in house H4
  forall(t in Day)
    sum(i in 10..11, j in Employee)
      x[i][j][t] <= 1;
      
}
