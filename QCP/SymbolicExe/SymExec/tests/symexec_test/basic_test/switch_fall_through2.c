enum MonthName {
    January, February, March, Unknown
};

enum MonthName intMonthToEnum(int month)
/*@ Require 0 <= month && month <= 3 && emp
    Ensure emp
*/
{
    enum MonthName res = Unknown;
    switch (month) {
        case 0:
        case 1: res = January; break;
        case 2: res = February; break;
        case 3: res = March; break;
    }
    return res;
}
