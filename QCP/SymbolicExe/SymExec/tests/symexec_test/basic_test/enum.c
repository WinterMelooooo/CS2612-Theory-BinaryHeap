enum MonthName {
    January, February, March, April, May, June, July, August, September, October, November, December 
};

int intMonthToEnum(int month)
/*@ Require 1 <= month && month <= 12 && emp
    Ensure __return == month - 1 && emp
*/
{
    switch (month) {
        case 1: return January;
        case 2: return February;
        case 3: return March;
        case 4: return April;
        case 5: return May;
        case 6: return June;
        case 7: return July;
        case 8: return August;
        case 9: return September;
        case 10: return October;
        case 11: return November;
        case 12: return December;
    }
}
