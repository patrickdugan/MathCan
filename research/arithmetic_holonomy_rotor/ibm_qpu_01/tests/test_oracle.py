import numpy as np
from scipy.linalg import expm
from hamiltonian import square_hamiltonian
from exact_oracle import (return_probability,four_phase_probabilities,
                          real_fourier_coefficient,exact_probabilities)
from phase_estimator import (quadrature,phase_from_quadrature,wrap,
                             phase_fisher_information,monte_carlo)
from mask_comparison import four_phase_mask_identity,equal_budget_comparison
from shot_budget import shot_targets


def test_hamiltonian_matches_qubit_pauli_expression():
    x=np.array([[0,1],[1,0]])
    y=np.array([[0,-1j],[1j,0]])
    z=np.diag([1,-1]);identity=np.eye(2);n=(identity-z)/2
    nx=np.kron(identity,n);ny=np.kron(n,identity)
    xx=np.kron(identity,x);xy=np.kron(x,identity);yy=np.kron(y,identity)
    theta=.62
    # The y flip is conditioned on the x (q0) occupation.
    h=(np.log(2)*nx+np.log(3)*ny+xx+
       np.kron(x,identity-n)+np.kron(np.cos(theta)*x+np.sin(theta)*y,n))
    assert np.allclose(h,square_hamiltonian(theta))


def test_reference_probabilities_and_coefficient():
    assert abs(return_probability(1.6,0)-.033829938394634)<1e-12
    assert abs(return_probability(1.6,np.pi)-.543163262832567)<1e-12
    assert abs(real_fourier_coefficient(1.6)+.25509419580938)<1e-9


def test_matrix_exp_unitarity_and_gauge_tree():
    for theta in [0,.1,.73,np.pi]:
        h=square_hamiltonian(theta)
        u=expm(-1j*h*1.6)
        assert np.allclose(u.conj().T@u,np.eye(4),atol=1e-12)
        assert np.isclose(exact_probabilities(h,1.6).sum(),1)
    for theta in np.linspace(0,2*np.pi,11):
        assert abs(return_probability(.9,theta,broken=True)-return_probability(.9,0,broken=True))<1e-12


def test_signed_four_phase_calibration():
    a1=real_fourier_coefficient(1.6)
    for theta in [-1.25,-.73,0,.73,1.25]:
        z=quadrature(four_phase_probabilities(1.6,theta))
        estimated=phase_from_quadrature(z,a1)
        assert abs(wrap(estimated-theta))<.003
    assert a1<0  # The sign must be divided out before taking the argument.


def test_fourier_aliasing_and_quadratures():
    n=128
    t=1.6;theta=.73
    # Second harmonic must vanish in the four-phase quadrature.
    z=quadrature(np.cos(2*(theta+np.arange(4)*np.pi/2)))
    assert abs(z)<1e-12
    # Third harmonic aliases into e^{-3i theta}, as documented.
    z=quadrature(np.cos(3*(theta+np.arange(4)*np.pi/2)))
    assert abs(z-np.exp(-3j*theta))<1e-12


def test_analytic_fisher_and_shot_budget():
    vals=phase_fisher_information(1.6,.73,8192,nuisance=True)
    assert 1000<vals['known_response_fisher']<3000
    assert vals['nuisance_crlb_rad2']>=vals['known_response_crlb_rad2']-1e-8
    assert shot_targets()['needed_total_shots_crlb']>0


def test_shot_monte_carlo_and_mask_equality():
    samples=monte_carlo(1.6,.73,8192,replicates=1000)
    assert .8<samples['rmse_deg']<2.5
    control=four_phase_mask_identity(1.6,.73)
    assert control['absolute_discrepancy']<1e-10
    comparison=equal_budget_comparison(1.6,.73,8192,replicates=200)
    assert comparison['phase_settings_masked']==64
    assert comparison['masked_rmse_deg']>comparison['intact_rmse_deg']
