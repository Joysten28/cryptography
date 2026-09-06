/**
 * Linear Congruential Generator (LCG) Virtual Laboratory
 * Core JavaScript Logic Engine
 *
 * Implements:
 * - Safe BigInt LCG recurrence calculations
 * - Step-by-step mathematical breakdown formatting
 * - Dynamic data table rendering
 * - Dual Chart.js visualizations (Line Chart + 2D Phase-space Scatter Plot)
 * - Floyd's Cycle Detection & Hull-Dobell Theorem Verification
 * - Automated Unit Test Suite execution
 * - Theme toggling
 */

document.addEventListener('DOMContentLoaded', () => {
    // UI Elements
    const form = document.getElementById('lcgForm');
    const seedInput = document.getElementById('seedInput');
    const aInput = document.getElementById('aInput');
    const cInput = document.getElementById('cInput');
    const mInput = document.getElementById('mInput');
    const nInput = document.getElementById('nInput');

    const btnGenerate = document.getElementById('btnGenerate');
    const btnReset = document.getElementById('btnReset');
    const btnRunTests = document.getElementById('btnRunTests');

    const validationAlert = document.getElementById('validationAlert');
    const validationText = document.getElementById('validationText');

    const themeToggle = document.getElementById('themeToggle');

    // Pagination for step-by-step
    const btnPrevSteps = document.getElementById('btnPrevSteps');
    const btnNextSteps = document.getElementById('btnNextSteps');
    const stepRangeLabel = document.getElementById('stepRangeLabel');
    const stepContainer = document.getElementById('stepBreakdownContainer');

    let currentStepPage = 0;
    const STEPS_PER_PAGE = 10;
    let currentSequenceData = [];

    // Chart instances
    let lineChart = null;
    let scatterChart = null;

    // Predefined Unit Test Cases
    const UNIT_TESTS = [
        {
            id: 1,
            name: "Test 1: Default Assignment Case",
            params: { seed: 7, a: 5, c: 3, m: 16, n: 5 },
            expected: [6, 1, 8, 11, 10],
            description: "Standard LCG with m=16, a=5, c=3, seed=7 for 5 iterations."
        },
        {
            id: 2,
            name: "Test 2: Lehmer Multiplicative Generator (c=0)",
            params: { seed: 1, a: 3, c: 0, m: 7, n: 6 },
            expected: [3, 2, 6, 4, 5, 1],
            description: "Multiplicative LCG with prime modulus m=7 and seed=1, including the repeated state at iteration 6."
        },
        {
            id: 3,
            name: "Test 3: Hull-Dobell Full Period Sequence",
            params: { seed: 0, a: 5, c: 7, m: 8, n: 8 },
            expected: [7, 2, 1, 4, 3, 6, 5, 0],
            description: "Full period generator (P=8) traversing all state space integers and repeating the seed at iteration 8."
        },
        {
            id: 4,
            name: "Test 4: Power of 2 Modulus LCG",
            params: { seed: 3, a: 5, c: 1, m: 16, n: 4 },
            expected: [0, 1, 6, 15],
            description: "Standard power-of-two modulus LCG verification."
        },
        {
            id: 5,
            name: "Test 5: Flawed RANDU Generator Initial Steps",
            params: { seed: 1, a: 65539, c: 0, m: 2147483648, n: 3 },
            expected: [65539, 393225, 1769499],
            description: "Historical RANDU algorithm sequence step calculation."
        }
    ];

    /* ==========================================================================
       Mathematical Helper Functions (BigInt & Number Theory)
       ========================================================================== */

    /**
     * Compute greatest common divisor (GCD) using Euclidean Algorithm
     */
    function gcd(a, b) {
        a = BigInt(a);
        b = BigInt(b);
        while (b !== 0n) {
            let temp = b;
            b = a % b;
            a = temp;
        }
        return a;
    }

    /**
     * Get unique prime factors of a BigInt number
     */
    function getPrimeFactors(n) {
        n = BigInt(n);
        const factors = new Set();
        let d = 2n;
        while (d * d <= n) {
            while (n % d === 0n) {
                factors.add(d);
                n /= d;
            }
            d++;
        }
        if (n > 1n) {
            factors.add(n);
        }
        return Array.from(factors);
    }

    /**
     * Core LCG Engine: generates N sequence elements using X_{n+1} = (a * X_n + c) mod m
     */
    function generateLCGSequence(seed, a, c, m, n) {
        const X0 = BigInt(seed);
        const A = BigInt(a);
        const C = BigInt(c);
        const M = BigInt(m);

        const sequence = [];
        let currState = X0;

        for (let i = 0; i < n; i++) {
            const nextState = (A * currState + C) % M;

            const stepVal = A * currState + C;
            const normVal = Number(nextState) / Number(M);

            sequence.push({
                n: i,
                Xn: Number(currState),
                a: Number(A),
                c: Number(C),
                m: Number(M),
                stepValStr: `${A} × ${currState} + ${C} = ${stepVal}`,
                calcStr: `(${A} × ${currState} + ${C}) mod ${M} = ${nextState}`,
                Xnext: Number(nextState),
                normVal: normVal.toFixed(6)
            });

            currState = nextState;
        }
        return sequence;
    }

    /* ==========================================================================
       Floyd's Cycle Detection & Hull-Dobell Verification
       ========================================================================== */

    /**
     * Cycle analysis using hash map state lookup for small N or full simulation
     */
    function analyzeCycle(seed, a, c, m) {
        const X0 = BigInt(seed);
        const A = BigInt(a);
        const C = BigInt(c);
        const M = BigInt(m);

        const visited = new Map();
        let currState = X0;
        let step = 0;

        // Traverse state space up to max 100,000 steps
        while (!visited.has(currState) && step < 100000) {
            visited.set(currState, step);
            currState = (A * currState + C) % M;
            step++;
        }

        if (visited.has(currState)) {
            const firstSeenIndex = visited.get(currState);
            const cycleLength = step - firstSeenIndex;
            return {
                hasCycle: true,
                cycleLength: cycleLength,
                startIndex: firstSeenIndex,
                repeatState: Number(currState),
                maxPossible: Number(M),
                periodRatio: (cycleLength / Number(M) * 100).toFixed(1)
            };
        }

        return {
            hasCycle: false,
            cycleLength: step,
            startIndex: 0,
            repeatState: null,
            maxPossible: Number(M),
            periodRatio: "N/A"
        };
    }

    /**
     * Evaluate Hull-Dobell Theorem conditions for full period
     */
    function checkHullDobell(a, c, m) {
        const A = BigInt(a);
        const C = BigInt(c);
        const M = BigInt(m);

        // Condition 1: gcd(c, m) === 1
        const cGcdM = gcd(C, M);
        const cond1 = (cGcdM === 1n);

        // Condition 2: (a - 1) divisible by all prime factors of m
        const aMinus1 = A - 1n;
        const primeFactorsM = getPrimeFactors(M);
        let cond2 = true;
        const failedFactors = [];

        for (const p of primeFactorsM) {
            if (aMinus1 % p !== 0n) {
                cond2 = false;
                failedFactors.push(p.toString());
            }
        }

        // Condition 3: If m is divisible by 4, (a - 1) must be divisible by 4
        let cond3 = true;
        let cond3Applies = false;
        if (M % 4n === 0n) {
            cond3Applies = true;
            if (aMinus1 % 4n !== 0n) {
                cond3 = false;
            }
        }

        const overallFullPeriod = cond1 && cond2 && cond3;

        return {
            overallFullPeriod,
            cond1: {
                passed: cond1,
                text: `gcd(${c}, ${m}) = ${cGcdM}. ${cond1 ? 'Coprime (Passed)' : 'Not coprime (Failed)'}`
            },
            cond2: {
                passed: cond2,
                text: `Prime factors of ${m}: {${primeFactorsM.join(', ')}}. ${cond2 ? 'All factors divide (a-1)=' + aMinus1 : 'Failed for factor(s): ' + failedFactors.join(', ')}`
            },
            cond3: {
                passed: cond3,
                applies: cond3Applies,
                text: cond3Applies
                    ? `4 divides ${m}, and 4 ${cond3 ? 'divides' : 'does NOT divide'} (a-1)=${aMinus1}.`
                    : `${m} is not divisible by 4 (Condition trivially holds).`
            }
        };
    }

    /* ==========================================================================
       UI Validation & Rendering
       ========================================================================== */

    function validateInputs() {
        const seed = parseInt(seedInput.value, 10);
        const a = parseInt(aInput.value, 10);
        const c = parseInt(cInput.value, 10);
        const m = parseInt(mInput.value, 10);
        const n = parseInt(nInput.value, 10);

        if (isNaN(seed) || isNaN(a) || isNaN(c) || isNaN(m) || isNaN(n)) {
            showError("All parameter fields must contain valid integer numbers.");
            return null;
        }

        if (m <= 0) {
            showError("Modulus (m) must be a positive integer strictly greater than 0.");
            return null;
        }

        if (seed < 0 || seed >= m) {
            showError(`Seed (X₀) must satisfy 0 ≤ X₀ < m (${m}).`);
            return null;
        }

        if (a < 0) {
            showError("Multiplier (a) cannot be negative.");
            return null;
        }

        if (c < 0) {
            showError("Increment (c) cannot be negative.");
            return null;
        }

        if (n < 1 || n > 1000) {
            showError("Number of iterations (N) must be between 1 and 1000.");
            return null;
        }

        hideError();
        return { seed, a, c, m, n };
    }

    function showError(msg) {
        validationText.textContent = msg;
        validationAlert.classList.remove('hidden');
    }

    function hideError() {
        validationAlert.classList.add('hidden');
    }

    /**
     * Render main simulation output across sections
     */
    function runSimulation() {
        const params = validateInputs();
        if (!params) return;

        const { seed, a, c, m, n } = params;
        currentSequenceData = generateLCGSequence(seed, a, c, m, n);

        // 1. Render Stats Summary
        document.getElementById('statModulus').textContent = m;
        const cycleInfo = analyzeCycle(seed, a, c, m);
        document.getElementById('statPeriod').textContent = cycleInfo.cycleLength;
        document.getElementById('statPeriodRatio').textContent = `${cycleInfo.periodRatio}%`;

        const hdInfo = checkHullDobell(a, c, m);
        const statHullDobellBadge = document.getElementById('statHullDobell');
        if (hdInfo.overallFullPeriod) {
            statHullDobellBadge.textContent = "Full Period (Passed)";
            statHullDobellBadge.className = "stat-value badge-success";
            document.getElementById('statDescription').innerHTML =
                `Generator satisfies all Hull-Dobell conditions! Full period length $P = m = ${m}$ is guaranteed.`;
        } else {
            statHullDobellBadge.textContent = "Partial Period";
            statHullDobellBadge.className = "stat-value badge-danger";
            document.getElementById('statDescription').innerHTML =
                `Generator fails Hull-Dobell conditions. Max period of $m=${m}$ is not achieved (Actual cycle length = ${cycleInfo.cycleLength}).`;
        }

        // 2. Render Step-by-Step Breakdown
        currentStepPage = 0;
        renderStepBreakdown();

        // 3. Render Table
        renderTable(currentSequenceData, cycleInfo);

        // 4. Render Charts
        renderCharts(currentSequenceData, m);

        // 5. Render Cycle Analysis Details
        renderCycleAnalysis(cycleInfo, hdInfo, a, c, m);

        document.getElementById('step-by-step').scrollIntoView({ behavior: 'smooth', block: 'start' });
    }

    /**
     * Step breakdown renderer with pagination
     */
    function renderStepBreakdown() {
        stepContainer.innerHTML = '';
        const total = currentSequenceData.length;
        const startIdx = currentStepPage * STEPS_PER_PAGE;
        const endIdx = Math.min(startIdx + STEPS_PER_PAGE, total);

        stepRangeLabel.textContent = `${startIdx + 1}-${endIdx} of ${total}`;
        btnPrevSteps.disabled = (currentStepPage === 0);
        btnNextSteps.disabled = (endIdx >= total);

        for (let i = startIdx; i < endIdx; i++) {
            const item = currentSequenceData[i];
            const card = document.createElement('div');
            card.className = 'step-card';
            card.innerHTML = `
                <span class="step-badge">Step ${item.n + 1}</span>
                <div class="step-math">
                    X<sub>${item.n + 1}</sub> = (${item.a} × <span class="var">${item.Xn}</span> + ${item.c}) mod ${item.m} 
                    ⇒ (${item.stepValStr.split('=')[1].trim()}) mod ${item.m} = <span class="result">${item.Xnext}</span>
                </div>
                <div class="step-output">
                    U<sub>${item.n + 1}</sub> = ${item.normVal}
                </div>
            `;
            stepContainer.appendChild(card);
        }
    }

    btnPrevSteps.addEventListener('click', () => {
        if (currentStepPage > 0) {
            currentStepPage--;
            renderStepBreakdown();
        }
    });

    btnNextSteps.addEventListener('click', () => {
        if ((currentStepPage + 1) * STEPS_PER_PAGE < currentSequenceData.length) {
            currentStepPage++;
            renderStepBreakdown();
        }
    });

    /**
     * Render sequence table
     */
    function renderTable(data, cycleInfo) {
        const tbody = document.getElementById('sequenceTableBody');
        tbody.innerHTML = '';

        data.forEach((row, idx) => {
            const tr = document.createElement('tr');
            // Highlight repeat entry point if cycle exists
            if (cycleInfo.hasCycle && cycleInfo.startIndex === row.n) {
                tr.className = 'row-repeat';
                tr.title = 'Cycle repetition starts here!';
            }

            tr.innerHTML = `
                <td><strong>n = ${row.n}</strong></td>
                <td>X<sub>${row.n}</sub> = ${row.Xn}</td>
                <td>(${row.a} × ${row.Xn} + ${row.c}) mod ${row.m}</td>
                <td><strong>X<sub>${row.n + 1}</sub> = ${row.Xnext}</strong></td>
                <td>${row.normVal}</td>
            `;
            tbody.appendChild(tr);
        });
    }

    /**
     * Render Chart.js Visualizations
     */
    function renderCharts(data, modulus) {
        const isDark = !document.body.classList.contains('light-theme');
        const gridColor = isDark ? 'rgba(255, 255, 255, 0.08)' : 'rgba(0, 0, 0, 0.08)';
        const textColor = isDark ? '#94a3b8' : '#475569';

        const labels = data.map(d => `Step ${d.n + 1}`);
        const xNextValues = data.map(d => d.Xnext);

        // 1. Line Chart: Values vs Iteration
        const lineCtx = document.getElementById('lineChart').getContext('2d');
        if (lineChart) lineChart.destroy();

        lineChart = new Chart(lineCtx, {
            type: 'line',
            data: {
                labels: labels,
                datasets: [{
                    label: 'Generated Value (Xₙ₊₁)',
                    data: xNextValues,
                    borderColor: '#38bdf8',
                    backgroundColor: 'rgba(56, 189, 248, 0.15)',
                    borderWidth: 2,
                    pointBackgroundColor: '#2dd4bf',
                    pointRadius: 4,
                    pointHoverRadius: 6,
                    fill: true,
                    tension: 0.2
                }]
            },
            options: {
                responsive: true,
                maintainAspectRatio: false,
                plugins: {
                    legend: { labels: { color: textColor, font: { family: 'Inter' } } },
                    tooltip: {
                        callbacks: {
                            label: (ctx) => `X = ${ctx.raw} (Normalized: ${(ctx.raw / modulus).toFixed(4)})`
                        }
                    }
                },
                scales: {
                    x: {
                        grid: { color: gridColor },
                        ticks: { color: textColor }
                    },
                    y: {
                        min: 0,
                        max: modulus,
                        grid: { color: gridColor },
                        ticks: { color: textColor }
                    }
                }
            }
        });

        // 2. Scatter Plot: Phase Space (X_n vs X_{n+1})
        const scatterCtx = document.getElementById('scatterChart').getContext('2d');
        if (scatterChart) scatterChart.destroy();

        const scatterPoints = data.map(d => ({ x: d.Xn, y: d.Xnext }));

        scatterChart = new Chart(scatterCtx, {
            type: 'scatter',
            data: {
                datasets: [{
                    label: 'Phase Space Pair (Xₙ, Xₙ₊₁)',
                    data: scatterPoints,
                    backgroundColor: '#a855f7',
                    borderColor: '#a855f7',
                    pointRadius: 5,
                    pointHoverRadius: 7
                }]
            },
            options: {
                responsive: true,
                maintainAspectRatio: false,
                plugins: {
                    legend: { labels: { color: textColor, font: { family: 'Inter' } } },
                    tooltip: {
                        callbacks: {
                            label: (ctx) => `(Xₙ: ${ctx.raw.x}, Xₙ₊₁: ${ctx.raw.y})`
                        }
                    }
                },
                scales: {
                    x: {
                        title: { display: true, text: 'Current State Xₙ', color: textColor },
                        min: 0,
                        max: modulus,
                        grid: { color: gridColor },
                        ticks: { color: textColor }
                    },
                    y: {
                        title: { display: true, text: 'Next State Xₙ₊₁', color: textColor },
                        min: 0,
                        max: modulus,
                        grid: { color: gridColor },
                        ticks: { color: textColor }
                    }
                }
            }
        });
    }

    /**
     * Render Cycle & Hull-Dobell detailed cards
     */
    function renderCycleAnalysis(cycleInfo, hdInfo, a, c, m) {
        document.getElementById('cycLengthVal').textContent = cycleInfo.cycleLength;
        document.getElementById('cycStartIndexVal').textContent = cycleInfo.hasCycle
            ? `Iteration ${cycleInfo.startIndex} (Value: ${cycleInfo.repeatState})`
            : `No cycle repeat within current sample`;
        document.getElementById('cycMaxVal').textContent = m;
        document.getElementById('cycRatioVal').textContent = `${cycleInfo.periodRatio}% (${hdInfo.overallFullPeriod ? 'Full Period' : 'Partial Period'})`;

        // Hull Dobell condition rendering
        const cond1El = document.getElementById('hdCondition1');
        const cond2El = document.getElementById('hdCondition2');
        const cond3El = document.getElementById('hdCondition3');

        updateCondUI(cond1El, hdInfo.cond1, 'hdCond1Text');
        updateCondUI(cond2El, hdInfo.cond2, 'hdCond2Text');
        updateCondUI(cond3El, hdInfo.cond3, 'hdCond3Text');
    }

    function updateCondUI(element, condObj, textId) {
        const textEl = document.getElementById(textId);
        const iconEl = element.querySelector('.condition-icon');
        textEl.textContent = condObj.text;

        if (condObj.passed) {
            element.classList.remove('failed');
            iconEl.className = 'fa-solid fa-check condition-icon';
        } else {
            element.classList.add('failed');
            iconEl.className = 'fa-solid fa-xmark condition-icon';
        }
    }

    /* ==========================================================================
       Automated Unit Test Suite Runner
       ========================================================================== */

    function runUnitTestSuite() {
        const container = document.getElementById('testResultsContainer');
        container.innerHTML = '';

        let passedCount = 0;
        const totalTests = UNIT_TESTS.length;

        UNIT_TESTS.forEach(test => {
            const { seed, a, c, m, n } = test.params;
            const resultData = generateLCGSequence(seed, a, c, m, n);
            const actualSequence = resultData.map(d => d.Xnext);

            const isPassed = (actualSequence.length === test.expected.length) &&
                actualSequence.every((val, idx) => val === test.expected[idx]);

            if (isPassed) passedCount++;

            const card = document.createElement('div');
            card.className = 'test-card';
            card.innerHTML = `
                <div class="test-card-header">
                    <div class="test-title">
                        <i class="fa-solid ${isPassed ? 'fa-circle-check text-accent' : 'fa-circle-xmark text-danger'}"></i>
                        ${test.name}
                    </div>
                    <span class="badge ${isPassed ? 'badge-pass' : 'badge-fail'}">
                        ${isPassed ? 'PASS' : 'FAIL'}
                    </span>
                </div>
                <p style="font-size: 0.85rem; color: var(--text-muted);">${test.description}</p>
                <div class="test-params">
                    Parameters: X₀=${seed}, a=${a}, c=${c}, m=${m}, N=${n}
                </div>
                <div class="test-comparison">
                    <div class="comp-box">
                        <span class="comp-label">Expected Output:</span>
                        [${test.expected.join(', ')}]
                    </div>
                    <div class="comp-box">
                        <span class="comp-label">Actual Output:</span>
                        [${actualSequence.join(', ')}]
                    </div>
                </div>
            `;
            container.appendChild(card);
        });

        // Summary Badge update
        const summaryBadge = document.getElementById('testSummaryBadge');
        summaryBadge.textContent = `${passedCount} / ${totalTests} Passed`;
        if (passedCount === totalTests) {
            summaryBadge.className = 'badge badge-pass';
        } else {
            summaryBadge.className = 'badge badge-fail';
        }
    }

    /* ==========================================================================
       Event Listeners & Initialization
       ========================================================================== */

    btnGenerate.addEventListener('click', runSimulation);

    btnReset.addEventListener('click', () => {
        seedInput.value = 0;
        aInput.value = 0;
        cInput.value = 0;
        mInput.value = 0;
        nInput.value = 0;
        hideError();
    });

    btnRunTests.addEventListener('click', () => {
        runUnitTestSuite();
        document.getElementById('tests').scrollIntoView({ behavior: 'smooth' });
    });

    // Theme Switcher
    themeToggle.addEventListener('click', () => {
        document.body.classList.toggle('light-theme');
        const icon = themeToggle.querySelector('i');
        if (document.body.classList.contains('light-theme')) {
            icon.className = 'fa-solid fa-sun';
        } else {
            icon.className = 'fa-solid fa-moon';
        }
        if (currentSequenceData.length > 0) {
            renderCharts(currentSequenceData, parseInt(mInput.value, 10));
        }
    });

    // Auto-initialize simulation and test suite on load
    runSimulation();
    runUnitTestSuite();
});
