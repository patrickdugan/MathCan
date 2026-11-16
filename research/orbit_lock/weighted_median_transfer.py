"""OLM-22 dependency-free exact Fraction weighted median and transfer witnesses."""
from fractions import Fraction as F


def q(x):
    return x if isinstance(x,F) else F(x)


def weighted_median_lad(rows,clip=F(2)):
    """Rows: (puzzle, slot, source residual x, target residual y)."""
    if not rows:raise ValueError('calibration observations required')
    if clip<=0:raise ValueError('positive symmetric bound required')
    points=[]
    for p,j,x,y in rows:
        x,y=q(x),q(y)
        if x:
            points.append((y/x,int(p),int(j),abs(x)))
    if not points:raise ValueError('degenerate source feature residual')
    points.sort(key=lambda r:(r[0],r[1],r[2]))
    weight=sum((r[3] for r in points),F(0))
    running=F(0)
    for ratio,p,j,w in points:
        running+=w
        if 2*running>=weight:
            return min(clip,max(-clip,ratio))
    raise ArithmeticError('finite sorted weighted median failed')


def ridge(rows):
    xx=sum((q(x)*q(x) for _,_,x,y in rows),F(0))
    xy=sum((q(x)*q(y) for _,_,x,y in rows),F(0))
    if xx==0:raise ValueError('degenerate source residual ridge')
    return min(F(2),max(F(-2),F(20,21)*xy/xx))


def mae(rows,beta):
    if not rows:raise ValueError('nonempty calibration source required')
    beta=q(beta)
    return sum((abs(q(y)-beta*q(x)) for _,_,x,y in rows),F(0))/len(rows)


def calibration_failure_example():
    cal=[(0,j,F(1),F(0) if j<7 else F(2)) for j in range(10)]
    test=[(1,j,F(1),F(2)) for j in range(10)]
    lad=weighted_median_lad(cal)
    old=ridge(cal)
    return {'lad':lad,'ridge':old,
            'cal_LAD_MAE':mae(cal,lad),'cal_ridge_MAE':mae(cal,old),
            'test_LAD_MAE':mae(test,lad),'test_ridge_MAE':mae(test,old),
            'same_source_marginal':all(x==1 for _,_,x,y in cal+test)}


def lower_median_tie_example():
    rows=[(0,0,1,0),(0,1,1,2)]
    return {'lad':weighted_median_lad(rows),
            'zero_loss':mae(rows,F(0)),
            'two_loss':mae(rows,F(2)),
            'one_loss':mae(rows,F(1))}


def finite_coupling_bound(pairs,beta):
    """Pairs (x,y,xprime,yprime) with uniform empirical coupling."""
    if not pairs:raise ValueError('joint source/target coupling required')
    b=q(beta)
    if abs(b)>2:raise ValueError('frozen beta outside registered clip')
    left=sum((abs(q(y)-b*q(x)) for x,y,xp,yp in pairs),F(0))/len(pairs)
    right=sum((abs(q(yp)-b*q(xp)) for x,y,xp,yp in pairs),F(0))/len(pairs)
    bound=sum((abs(q(yp)-q(y))+2*abs(q(xp)-q(x)) for x,y,xp,yp in pairs),F(0))/len(pairs)
    return {'absolute_risk_shift':abs(left-right),'coupled_l1_bound':bound}


def sharp_coupling_example():
    return finite_coupling_bound([(F(0),F(0),F(3,5),F(0))],F(2))


if __name__=='__main__':
    print(calibration_failure_example())
    print(lower_median_tie_example())
    print(sharp_coupling_example())
