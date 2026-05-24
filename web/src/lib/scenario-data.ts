/**
 * Synthetic demo data + policy for the financial-institution scenario.
 *
 * Schema matches the real Kaggle `transactions-fraud-datasets` (paper §5)
 * but rows are hand-rolled so we don't ship a third-party dataset. The
 * sensitive-column list is what the policy must protect.
 */

export interface Catalog {
  [relation: string]: string[];
}

export interface Grant {
  principal: string;
  relation: string;
  columns: string[];
}

export type Policy = Grant[];

/** Catalog — relation → ordered column list. Mirrors postern-core. */
export const CATALOG: Catalog = {
  users_data: ["id", "name", "email", "ssn", "region", "age"],
  cards_data: [
    "card_id",
    "user_id",
    "card_number",
    "card_type",
    "limit",
    "activated",
  ],
  transactions_data: [
    "txn_id",
    "card_id",
    "amount",
    "merchant",
    "timestamp",
  ],
};

/** Columns the policy treats as PII / PAN — never granted to anyone. */
export const SENSITIVE: Record<string, ReadonlyArray<string>> = {
  users_data: ["email", "ssn"],
  cards_data: ["card_number"],
  transactions_data: [],
};

export const PRINCIPALS = ["CRM", "CardOps", "FraudRisk"] as const;
export type Principal = (typeof PRINCIPALS)[number];

/**
 * Demo policy — verbatim Datalog desugaring of
 * `scenarios/financial-institution/policy.postern`.
 *
 *   grant CRM       on users_data        { id, name, region, age }
 *   grant CardOps   on cards_data        { card_id, card_type, limit, activated }
 *   grant FraudRisk on transactions_data { txn_id, card_id, amount, merchant, timestamp }
 *   grant FraudRisk on users_data        { id, region }
 */
export const POLICY: Policy = [
  {
    principal: "CRM",
    relation: "users_data",
    columns: ["id", "name", "region", "age"],
  },
  {
    principal: "CardOps",
    relation: "cards_data",
    columns: ["card_id", "card_type", "limit", "activated"],
  },
  {
    principal: "FraudRisk",
    relation: "transactions_data",
    columns: ["txn_id", "card_id", "amount", "merchant", "timestamp"],
  },
  {
    principal: "FraudRisk",
    relation: "users_data",
    columns: ["id", "region"],
  },
];

/** Datalog desugaring of the policy: one fact per column-grant pair. */
export function policyAsDatalog(policy: Policy): string {
  const facts: string[] = [];
  for (const g of policy) {
    for (const c of g.columns) {
      facts.push(`right("${g.principal}", "${g.relation}", "${c}").`);
    }
  }
  return facts.join("\n");
}

/** Synthetic rows for each relation. 5 each. */
export const TABLES: Record<string, Array<Record<string, string | number>>> = {
  users_data: [
    {
      id: "u_001",
      name: "Alex Chen",
      email: "alex.chen@example.com",
      ssn: "123-45-6789",
      region: "EU-West",
      age: 34,
    },
    {
      id: "u_002",
      name: "Priya Rao",
      email: "priya.rao@example.com",
      ssn: "234-56-7891",
      region: "APAC",
      age: 41,
    },
    {
      id: "u_003",
      name: "Jamal Khan",
      email: "jamal.khan@example.com",
      ssn: "345-67-8912",
      region: "EU-West",
      age: 29,
    },
    {
      id: "u_004",
      name: "Lin Wei",
      email: "lin.wei@example.com",
      ssn: "456-78-9123",
      region: "APAC",
      age: 52,
    },
    {
      id: "u_005",
      name: "Sara Müller",
      email: "sara.mueller@example.com",
      ssn: "567-89-1234",
      region: "EU-West",
      age: 23,
    },
  ],
  cards_data: [
    {
      card_id: "c_4001",
      user_id: "u_001",
      card_number: "4111-1111-1111-1111",
      card_type: "credit",
      limit: 15000,
      activated: 1,
    },
    {
      card_id: "c_4002",
      user_id: "u_002",
      card_number: "5500-0000-0000-0004",
      card_type: "credit",
      limit: 8000,
      activated: 1,
    },
    {
      card_id: "c_4003",
      user_id: "u_003",
      card_number: "3400-0000-0000-009",
      card_type: "amex",
      limit: 25000,
      activated: 0,
    },
    {
      card_id: "c_4004",
      user_id: "u_004",
      card_number: "6011-0000-0000-0004",
      card_type: "debit",
      limit: 2500,
      activated: 1,
    },
    {
      card_id: "c_4005",
      user_id: "u_005",
      card_number: "4111-2222-3333-4444",
      card_type: "credit",
      limit: 5000,
      activated: 1,
    },
  ],
  transactions_data: [
    {
      txn_id: "t_9001",
      card_id: "c_4001",
      amount: 42.5,
      merchant: "ACME Coffee",
      timestamp: "2026-05-23T08:14:00Z",
    },
    {
      txn_id: "t_9002",
      card_id: "c_4002",
      amount: 1299.0,
      merchant: "Online Electronics",
      timestamp: "2026-05-23T14:02:00Z",
    },
    {
      txn_id: "t_9003",
      card_id: "c_4005",
      amount: 17.85,
      merchant: "Bakery One",
      timestamp: "2026-05-24T09:31:00Z",
    },
    {
      txn_id: "t_9004",
      card_id: "c_4001",
      amount: 540.0,
      merchant: "Airline X",
      timestamp: "2026-05-24T17:11:00Z",
    },
    {
      txn_id: "t_9005",
      card_id: "c_4004",
      amount: 8.4,
      merchant: "Transit Pass",
      timestamp: "2026-05-25T07:02:00Z",
    },
  ],
};
