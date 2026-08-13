use std::thread;

use pasta_curves::{
    group::{Curve, Group},
    pallas, vesta,
};

#[test]
fn concurrent_calls_are_independent() {
    let workers = (0..4)
        .map(|worker| {
            thread::spawn(move || {
                let pallas_scalars = (0..128)
                    .map(|index| pallas::Scalar::from(worker * 128 + index + 1))
                    .collect::<Vec<_>>();
                let pallas_points = pallas_scalars
                    .iter()
                    .map(|scalar| (pallas::Point::generator() * scalar).to_affine())
                    .collect::<Vec<_>>();
                let expected_pallas = pallas_points
                    .iter()
                    .zip(&pallas_scalars)
                    .fold(pallas::Point::identity(), |sum, (point, scalar)| {
                        sum + *point * *scalar
                    });
                assert_eq!(
                    pasta_msm::pallas_vartime(&pallas_points, &pallas_scalars),
                    expected_pallas
                );

                let vesta_scalars = (0..128)
                    .map(|index| vesta::Scalar::from(worker * 128 + index + 1))
                    .collect::<Vec<_>>();
                let vesta_points = vesta_scalars
                    .iter()
                    .map(|scalar| (vesta::Point::generator() * scalar).to_affine())
                    .collect::<Vec<_>>();
                let expected_vesta = vesta_points
                    .iter()
                    .zip(&vesta_scalars)
                    .fold(vesta::Point::identity(), |sum, (point, scalar)| {
                        sum + *point * *scalar
                    });
                assert_eq!(
                    pasta_msm::vesta_vartime(&vesta_points, &vesta_scalars),
                    expected_vesta
                );
            })
        })
        .collect::<Vec<_>>();

    for worker in workers {
        worker.join().expect("worker must not panic");
    }
}
